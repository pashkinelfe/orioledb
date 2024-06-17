/*-------------------------------------------------------------------------
 *
 * recovery.c
 *		Support for logical decoding of OrioleDB tables.
 *
 * Copyright (c) 2024, Oriole DB Inc.
 *
 * IDENTIFICATION
 *	  contrib/orioledb/src/recovery/logical.c
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "orioledb.h"

#include "btree/page_contents.h"
#include "catalog/sys_trees.h"
#include "recovery/logical.h"
#include "recovery/recovery.h"
#include "recovery/internal.h"
#include "recovery/wal.h"
#include "tableam/descr.h"
#include "tuple/slot.h"

#include "catalog/pg_tablespace.h"
#include "replication/origin.h"
#include "replication/reorderbuffer.h"
#include "replication/snapbuild.h"
#include "access/toast_compression.h"

static void
tts_copy_identity(TupleTableSlot *srcSlot, TupleTableSlot *dstSlot,
				  OIndexDescr *idx)
{
	int			i;
	int			nattrs = dstSlot->tts_tupleDescriptor->natts;

	slot_getallattrs(srcSlot);

	dstSlot->tts_nvalid = nattrs;
	for (i = 0; i < nattrs; i++)
	{
		dstSlot->tts_isnull[i] = true;
		dstSlot->tts_values[i] = (Datum) 0;
	}

	for (i = 0; i < idx->nonLeafTupdesc->natts; i++)
	{
		int			attnum;

		attnum = idx->fields[i].tableAttnum - 1;
		if (attnum >= 0)
		{
			dstSlot->tts_values[i] = srcSlot->tts_values[i];
			dstSlot->tts_isnull[i] = srcSlot->tts_isnull[i];
		}
		else if (attnum == -1)
		{
			dstSlot->tts_tid = srcSlot->tts_tid;
		}
	}
}
static ReorderBufferTupleBuf *
record_buffer_tuple(ReorderBuffer *reorder, HeapTuple htup)
{
	HeapTuple	changeTup;
	ReorderBufferTupleBuf *result;

	result = ReorderBufferGetTupleBuf(reorder, htup->t_len);

	changeTup = &result->tuple;
	changeTup->t_tableOid = InvalidOid;
	changeTup->t_len = htup->t_len;
	changeTup->t_self = htup->t_self;
	memcpy(changeTup->t_data, htup->t_data, htup->t_len);

	return result;
}

static ReorderBufferTupleBuf *
record_buffer_tuple_slot(ReorderBuffer *reorder, TupleTableSlot *slot)
{
	HeapTuple	htup;
	bool		freeHtup;
	ReorderBufferTupleBuf *result;

	htup = ExecFetchSlotHeapTuple(slot, false, &freeHtup);

	result = record_buffer_tuple(reorder, htup);

	if (freeHtup)
		heap_freetuple(htup);

	return result;
}


/*
 * Handle OrioleDB records for LogicalDecodingProcessRecord().
 */
void
orioledb_decode(LogicalDecodingContext *ctx, XLogRecordBuffer *buf)
{
	XLogReaderState *record = buf->record;
	Pointer		startPtr = (Pointer) XLogRecGetData(record);
	Pointer		endPtr = startPtr + XLogRecGetDataLen(record);
	Pointer		ptr = startPtr;
	OTableDescr *descr = NULL;
	OIndexDescr *indexDescr = NULL;
	int			sys_tree_num = -1;
	ORelOids	cur_oids = {0, 0, 0};
	OXid		oxid = InvalidOXid;
	TransactionId logicalXid = InvalidTransactionId;
	uint8		rec_type;
	uint8		rec_flags;
	OffsetNumber length;
	OIndexType	ix_type = oIndexInvalid;
	TupleDescData 	*o_toast_tupDesc;
	TupleDescData   *heap_toast_tupDesc;
	uint16 		*chunk_seq;

	while (ptr < endPtr)
	{

		rec_type = *ptr & 0x0F;
		rec_flags = *ptr & 0xF0;
		ptr++;

		elog(INFO, "WAL_REC: %s %s", rec_type == WAL_REC_XID ? "XID" :
				rec_type == WAL_REC_COMMIT ? "COMMIT" :
				rec_type == WAL_REC_ROLLBACK ? "ROLLBACK" :
				rec_type == WAL_REC_JOINT_COMMIT ? "JOINT COMMIT" :
				rec_type == WAL_REC_RELATION ? "RELATION" :
				rec_type == WAL_REC_O_TABLES_META_LOCK ? "META LOCK" :
				rec_type == WAL_REC_O_TABLES_META_UNLOCK ? "META_UNLOCK" :
				rec_type == WAL_REC_TRUNCATE ? "TRUNCATE" :
				rec_type == WAL_REC_SAVEPOINT ? "SAVEPOINT" :
				rec_type == WAL_REC_ROLLBACK_TO_SAVEPOINT ? "ROLLBACK TO SAVEPOINT" :
				rec_type == WAL_REC_INSERT ? "INSERT" :
				rec_type == WAL_REC_UPDATE ? "UPDATE" :
				rec_type == WAL_REC_DELETE ? "DELETE" : "_UNKNOWN"
				,
				(rec_flags & WAL_REC_TOAST) ? "TOAST" : "");

		if (rec_type == WAL_REC_XID)
		{
			memcpy(&oxid, ptr, sizeof(oxid));
			ptr += sizeof(oxid);

			memcpy(&logicalXid, ptr, sizeof(TransactionId));
			ptr += sizeof(TransactionId);


		}
		else if (rec_type == WAL_REC_COMMIT || rec_type == WAL_REC_ROLLBACK)
		{
			OXid		xmin;
#if PG_VERSION_NUM >= 160000
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder);
#else
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder, InvalidTransactionId);
#endif

			memcpy(&xmin, ptr, sizeof(xmin));
			ptr += sizeof(xmin);

			ReorderBufferSetBaseSnapshot(ctx->reorder, logicalXid,
										 buf->origptr + (ptr - startPtr),
										 snap);
			snap->active_count++;

			ReorderBufferCommit(ctx->reorder, logicalXid, buf->origptr, buf->endptr,
								0, InvalidRepOriginId, buf->origptr + (ptr - startPtr));
			UpdateDecodingStats(ctx);

			oxid = InvalidOXid;
			logicalXid = InvalidTransactionId;
		}
		else if (rec_type == WAL_REC_JOINT_COMMIT)
		{
			TransactionId xid;
			OXid		xmin;
#if PG_VERSION_NUM >= 160000
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder);
#else
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder, InvalidTransactionId);
#endif

			memcpy(&xid, ptr, sizeof(xid));
			ptr += sizeof(xid);
			memcpy(&xmin, ptr, sizeof(xmin));
			ptr += sizeof(xmin);

			ReorderBufferSetBaseSnapshot(ctx->reorder, logicalXid,
										 buf->origptr + (ptr - startPtr),
										 snap);
			snap->active_count++;

			ReorderBufferCommit(ctx->reorder, logicalXid, buf->origptr, buf->endptr,
								0, InvalidRepOriginId, buf->origptr + (ptr - startPtr));
			UpdateDecodingStats(ctx);
		}
		else if (rec_type == WAL_REC_RELATION)
		{
			ix_type = *ptr;
			ptr++;
			memcpy(&cur_oids.datoid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&cur_oids.reloid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&cur_oids.relnode, ptr, sizeof(Oid));
			ptr += sizeof(Oid);

			if (IS_SYS_TREE_OIDS(cur_oids))
				sys_tree_num = cur_oids.relnode;
			else
				sys_tree_num = -1;

			if (sys_tree_num > 0)
			{
				descr = NULL;
				/* indexDescr = NULL; */
				Assert(sys_tree_get_storage_type(sys_tree_num) == BTreeStoragePersistence);
			}
			else if (ix_type == oIndexInvalid)
			{
				descr = o_fetch_table_descr(cur_oids);
				//indexDescr = o_fetch_index_descr(cur_oids, ix_type, false, NULL);
				indexDescr = descr ? GET_PRIMARY(descr) : NULL; 
			}
			else
			{
				Assert(ix_type == oIndexToast);
				indexDescr = o_fetch_index_descr(cur_oids, ix_type, false, NULL);
				descr = o_fetch_table_descr(indexDescr->tableOids);
				elog (INFO, "table natts: %u", descr->tupdesc->natts);
				o_toast_tupDesc = descr->toast->leafTupdesc;
				heap_toast_tupDesc = CreateTemplateTupleDesc(3);
				TupleDescInitEntry(heap_toast_tupDesc, (AttrNumber) 1, "chunk_id", OIDOID, -1, 0);
				TupleDescInitEntry(heap_toast_tupDesc, (AttrNumber) 2, "chunk_seq", INT4OID, -1, 0);
				TupleDescInitEntry(heap_toast_tupDesc, (AttrNumber) 3, "chunk_data", BYTEAOID, -1, 0);
				/* Ensure that the toast table doesn't itself get toasted */
				TupleDescAttr(heap_toast_tupDesc, 0)->attstorage = TYPSTORAGE_PLAIN;
				TupleDescAttr(heap_toast_tupDesc, 1)->attstorage = TYPSTORAGE_PLAIN;
				TupleDescAttr(heap_toast_tupDesc, 2)->attstorage = TYPSTORAGE_PLAIN;
				/* Toast field should not be compressed */
				TupleDescAttr(heap_toast_tupDesc, 0)->attcompression = InvalidCompressionMethod;
				TupleDescAttr(heap_toast_tupDesc, 1)->attcompression = InvalidCompressionMethod;
				TupleDescAttr(heap_toast_tupDesc, 2)->attcompression = InvalidCompressionMethod;
				chunk_seq = palloc0 (sizeof(uint32) * descr->tupdesc->natts);

				/*
				 * indexDescr = o_fetch_index_descr(cur_oids, ix_type, false,
				 * NULL);
				 */
			}
		}
		else if (rec_type == WAL_REC_O_TABLES_META_LOCK)
		{
			/* Skip */
		}
		else if (rec_type == WAL_REC_O_TABLES_META_UNLOCK)
		{
			ORelOids	oids;
			Oid			oldRelnode;

			memcpy(&oids.datoid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&oids.reloid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&oldRelnode, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&oids.relnode, ptr, sizeof(Oid));
			ptr += sizeof(Oid);

			/* Skip */
		}
		else if (rec_type == WAL_REC_TRUNCATE)
		{
			ORelOids	oids;

			memcpy(&oids.datoid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&oids.reloid, ptr, sizeof(Oid));
			ptr += sizeof(Oid);
			memcpy(&oids.relnode, ptr, sizeof(Oid));
			ptr += sizeof(Oid);

			/* Skip */
		}
		else if (rec_type == WAL_REC_SAVEPOINT)
		{
			SubTransactionId parentSubid;

			memcpy(&parentSubid, ptr, sizeof(SubTransactionId));
			ptr += sizeof(SubTransactionId);

			/* Skip */
		}
		else if (rec_type == WAL_REC_ROLLBACK_TO_SAVEPOINT)
		{
			SubTransactionId parentSubid;

			memcpy(&parentSubid, ptr, sizeof(SubTransactionId));
			ptr += sizeof(SubTransactionId);

			/* Skip */
		}
		else
		{
			OFixedTuple tuple;
			ReorderBufferChange *change;

			Assert(rec_type == WAL_REC_INSERT || rec_type == WAL_REC_UPDATE || rec_type == WAL_REC_DELETE);

			ReorderBufferProcessXid(ctx->reorder, logicalXid, buf->origptr + (ptr - startPtr));

			tuple.tuple.formatFlags = *ptr;
			ptr++;

			memcpy(&length, ptr, sizeof(OffsetNumber));
			ptr += sizeof(OffsetNumber);


			if ((ix_type == oIndexInvalid || ix_type == oIndexToast) &&
				cur_oids.datoid == ctx->slot->data.database)
			{
				Assert(descr != NULL);
				memcpy(tuple.fixedData, ptr, length);
				tuple.tuple.data = tuple.fixedData;

				if (rec_type == WAL_REC_INSERT)
				{

					change = ReorderBufferGetChange(ctx->reorder);
					change->action = REORDER_BUFFER_CHANGE_INSERT;
#if PG_VERSION_NUM >= 160000
					change->data.tp.rlocator.spcOid = DEFAULTTABLESPACE_OID;
					change->data.tp.rlocator.dbOid = cur_oids.datoid;
					change->data.tp.rlocator.relNumber = cur_oids.relnode;
#else
					change->data.tp.relnode.spcNode = DEFAULTTABLESPACE_OID;
					change->data.tp.relnode.dbNode = cur_oids.datoid;
					change->data.tp.relnode.relNode = cur_oids.relnode;
#endif

					elog(INFO, "datoid: %d, reloid: %d, relnode: %d", cur_oids.datoid, cur_oids.reloid, cur_oids.relnode);
					if (rec_flags & WAL_REC_TOAST)
                                        {
						uint32 id;
						uint16 attnum;
						uint32 offset;
						Datum  chunk_data;
						HeapTuple toasttup;
						Datum  t_values[3];
						bool   t_isnull[3];

						Assert(ix_type == oIndexToast);

						id = *((uint32*) o_fastgetattr_ptr(tuple.tuple, 1, o_toast_tupDesc, &descr->toast->leafSpec));
						attnum = *((uint16*) o_fastgetattr_ptr(tuple.tuple, 2, o_toast_tupDesc, &descr->toast->leafSpec));
						offset = *((uint32*) o_fastgetattr_ptr(tuple.tuple, 3, o_toast_tupDesc, &descr->toast->leafSpec));
						chunk_data = PointerGetDatum(o_fastgetattr_ptr(tuple.tuple, 4, o_toast_tupDesc, &descr->toast->leafSpec));

						elog(INFO, "id: %u, attnum: %u, offset: %u, length_get: %u, chunk_seq: %u, chunk_varsize: %u", id, attnum, offset, length, chunk_seq[attnum], VARSIZE(chunk_data)); 
//						SET_VARSIZE(&chunk_data, chunk_size + VARHDRSZ);
						t_values[0] = ObjectIdGetDatum(attnum + 10000);
						t_values[1] = Int32GetDatum(chunk_seq[attnum]);
						t_values[2] = chunk_data;
						t_isnull[0] = false;
						t_isnull[1] = false;
						t_isnull[2] = false;
						toasttup = heap_form_tuple(heap_toast_tupDesc, t_values, t_isnull);
						change->data.tp.newtuple = record_buffer_tuple(ctx->reorder, toasttup);
						change->data.tp.clear_toast_afterwards = false;

						heap_freetuple(toasttup);
						chunk_seq[attnum]++;
	//					volatile bool a = 1;
//                                      while (a)
  //                                              {
    //                                            pg_usleep(1000L);
      //                                         }
                                        }
					else
					{
						int 		ixnum = PrimaryIndexNumber;

						Assert(ix_type != oIndexToast);
						/* Primary table contains TOASTed attributes */
						if(descr->ntoastable > 0)
						{
							int 	     natts = descr->tupdesc->natts;
							Datum       *old_values = palloc(natts*sizeof(Datum));
							Datum	    *new_values = palloc(natts*sizeof(Datum));
							bool 	    *isnull = palloc(natts*sizeof(bool));
							int         ctid_off = indexDescr->primaryIsCtid ? 1 : 0;
							OFixedTuple newtuple;

							Assert(descr->toast);
							for (int i = 0; i < natts; i++)
							{
								old_values[i] = o_fastgetattr(tuple.tuple, i + 1, descr->tupdesc, &indexDescr->leafSpec, &isnull[i]);
								new_values[i] = old_values[i];
								Assert(!isnull);
							}
						
							/* Convert TOAST pointers */	
							for (int i = 0; i < descr->ntoastable; i++)
							{
								int toast_attn = descr->toastable[i] - ctid_off;
								OToastExternal ote;
								varatt_external ve;

								Assert(VARATT_IS_EXTERNAL_ORIOLEDB(old_values));
								ote = VARDATA_EXTERNAL(old_values[toast_attn]);
								ve.va_rawsize = ote.raw_size;
								ve.va_extinfo = ote.raw_size - VARHDRSZ;
								ve.va_toastrelid = descr->toast->oids->reloid; 
								ve.va_valueid = ObjectIdGetDatum(toast_attn + 10000);
								SET_VARTAG_EXTERNAL(new_values[toast_attn], VARTAG_ONDISK);
								memcpy(VARDATA_EXTERNAL(new_values[toast_attn]), &ve, sizeof(varatt_external);
							}
							
							newtuple.tuple = o_form_tuple(descr->tupdesc, &indexDescr->leafSpec,
							       	 		o_tuple_get_version(tuple.tuple), new_values, isnull);
						volatile bool a = 1;
	                                        while (a)
                                                {
                                                pg_usleep(1000L);
                                                }

							tts_orioledb_store_tuple(descr->newTuple, newtuple.tuple,
											 descr, COMMITSEQNO_INPROGRESS,
											 ixnum, false,
											 NULL);

						}
						else
						{
							tts_orioledb_store_tuple(descr->newTuple, tuple.tuple,
											 descr, COMMITSEQNO_INPROGRESS,
											 ixnum, false,
											 NULL);
						}
						change->data.tp.newtuple = record_buffer_tuple_slot(ctx->reorder, descr->newTuple);
						change->data.tp.clear_toast_afterwards = true;

					}


					ReorderBufferQueueChange(ctx->reorder, logicalXid,
											 buf->origptr + (ptr - startPtr),
											 change, (rec_flags & WAL_REC_TOAST));

				}
				else if (rec_type == WAL_REC_UPDATE)
				{
					tts_orioledb_store_tuple(descr->newTuple, tuple.tuple,
											 descr, COMMITSEQNO_INPROGRESS,
											 PrimaryIndexNumber, false,
											 NULL);
					tts_copy_identity(descr->newTuple, descr->oldTuple,
									  GET_PRIMARY(descr));

					change = ReorderBufferGetChange(ctx->reorder);
					change->action = REORDER_BUFFER_CHANGE_UPDATE;
					change->data.tp.oldtuple = record_buffer_tuple_slot(ctx->reorder, descr->oldTuple);
					change->data.tp.newtuple = record_buffer_tuple_slot(ctx->reorder, descr->newTuple);
					change->data.tp.clear_toast_afterwards = true;
#if PG_VERSION_NUM >= 160000
					change->data.tp.rlocator.spcOid = DEFAULTTABLESPACE_OID;
					change->data.tp.rlocator.dbOid = cur_oids.datoid;
					change->data.tp.rlocator.relNumber = cur_oids.relnode;
#else
					change->data.tp.relnode.spcNode = DEFAULTTABLESPACE_OID;
					change->data.tp.relnode.dbNode = cur_oids.datoid;
					change->data.tp.relnode.relNode = cur_oids.relnode;
#endif

					ReorderBufferQueueChange(ctx->reorder, logicalXid,
											 buf->origptr + (ptr - startPtr),
											 change, false);


				}
				else if (rec_type == WAL_REC_DELETE)
				{
					tts_orioledb_store_non_leaf_tuple(descr->oldTuple, tuple.tuple,
													  descr, COMMITSEQNO_INPROGRESS,
													  PrimaryIndexNumber, false,
													  NULL);

					change = ReorderBufferGetChange(ctx->reorder);
					change->action = REORDER_BUFFER_CHANGE_DELETE;
					change->data.tp.oldtuple = record_buffer_tuple_slot(ctx->reorder, descr->oldTuple);
					change->data.tp.clear_toast_afterwards = true;
#if PG_VERSION_NUM >= 160000
					change->data.tp.rlocator.spcOid = DEFAULTTABLESPACE_OID;
					change->data.tp.rlocator.dbOid = cur_oids.datoid;
					change->data.tp.rlocator.relNumber = cur_oids.relnode;
#else
					change->data.tp.relnode.spcNode = DEFAULTTABLESPACE_OID;
					change->data.tp.relnode.dbNode = cur_oids.datoid;
					change->data.tp.relnode.relNode = cur_oids.relnode;
#endif

					ReorderBufferQueueChange(ctx->reorder, logicalXid,
											 buf->origptr + (ptr - startPtr),
											 change, false);
				}
			}

			ptr += length;
		}
	}
}
