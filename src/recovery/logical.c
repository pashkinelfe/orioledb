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
#include "access/detoast.h"
#include "tuple/toast.h"

static uint32          *chunk_seq = NULL;
#ifdef USE_ASSERT_CHECKING
static uint32          *data_done = NULL;
#endif

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
record_buffer_tuple(ReorderBuffer *reorder, HeapTuple htup, bool freeHtup)
{
	HeapTuple	changeTup;
	ReorderBufferTupleBuf *result;

	result = ReorderBufferGetTupleBuf(reorder, htup->t_len);

	changeTup = &result->tuple;
	changeTup->t_tableOid = InvalidOid;
	changeTup->t_len = htup->t_len;
	changeTup->t_self = htup->t_self;
	memcpy(changeTup->t_data, htup->t_data, htup->t_len);

	if (freeHtup)
		heap_freetuple(htup);

	return result;
}

static ReorderBufferTupleBuf *
record_buffer_tuple_slot(ReorderBuffer *reorder, TupleTableSlot *slot)
{
	HeapTuple	htup;
	bool		freeHtup;
	ReorderBufferTupleBuf *result;

	htup = ExecFetchSlotHeapTuple(slot, false, &freeHtup);

	result = record_buffer_tuple(reorder, htup, freeHtup);

	return result;
}

/* entry for a hash table we use to map from xid to our transaction state */
typedef struct ReorderBufferTXNByIdEnt
{
	TransactionId xid;
	ReorderBufferTXN *txn;
} ReorderBufferTXNByIdEnt;

static ReorderBufferTXN *
get_reorder_buffer_txn(ReorderBuffer *rb, TransactionId xid)
{
	ReorderBufferTXNByIdEnt *ent;
	bool		found;

	if (TransactionIdIsValid(rb->by_txn_last_xid) &&
		rb->by_txn_last_xid == xid)
		return rb->by_txn_last_txn;

	/* search the lookup table */
	ent = (ReorderBufferTXNByIdEnt *)
		hash_search(rb->by_txn, &xid, HASH_FIND, &found);
	if (found)
		return ent->txn;
	else
		return NULL;
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
	TupleDescData 	*o_toast_tupDesc = NULL;
	TupleDescData   *heap_toast_tupDesc = NULL;

// 	elog(INFO, "ORIOLEDB_DECODE");	
	while (ptr < endPtr)
	{

		rec_type = *ptr & 0x0F;
		rec_flags = *ptr & 0xF0;
		ptr++;

		elog(INFO, "RECEIVE: %s %s", rec_type == WAL_REC_XID ? "XID" :
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
			dlist_iter	cur_txn_i;
			ReorderBufferTXN *txn;
#if PG_VERSION_NUM >= 160000
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder);
#else
			Snapshot	snap = SnapBuildGetOrBuildSnapshot(ctx->snapshot_builder, InvalidTransactionId);
#endif

			memcpy(&xmin, ptr, sizeof(xmin));
			ptr += sizeof(xmin);

			txn = get_reorder_buffer_txn(ctx->reorder, logicalXid);
			if (txn->toptxn)
				txn = txn->toptxn;

			ReorderBufferSetBaseSnapshot(ctx->reorder, logicalXid,
										 buf->origptr + (ptr - startPtr),
										 snap);
			snap->active_count++;

			dlist_foreach(cur_txn_i, &txn->subtxns)
			{
				ReorderBufferTXN *cur_txn;

				cur_txn = dlist_container(ReorderBufferTXN, node, cur_txn_i.cur);

				ReorderBufferCommitChild(ctx->reorder, txn->xid, cur_txn->xid,
										 buf->origptr, buf->endptr);

			}

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
				indexDescr = descr ? GET_PRIMARY(descr) : NULL;
			}
			else
			{
				Assert(ix_type == oIndexToast);
//				pk_natts = tupDesc->natts - TOAST_LEAF_FIELDS_NUM;
				indexDescr = o_fetch_index_descr(cur_oids, ix_type, false, NULL);
				descr = o_fetch_table_descr(indexDescr->tableOids);
				o_toast_tupDesc = descr->toast->leafTupdesc;
				/* Init heap tupledesc for toast table */
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
				if (!chunk_seq)
					chunk_seq = palloc0 (sizeof(uint32) * descr->tupdesc->natts);
#ifdef USE_ASSERT_CHECKING
				if (!data_done)
					data_done = palloc0 (sizeof(uint32) * descr->tupdesc->natts);
#endif
				/*
				 * indexDescr = o_fetch_index_descr(cur_oids, ix_type, false,
				 * NULL);
				 */
			}
			
			if (descr && descr->toast)
				elog(INFO, "reloid: %d natts: %u toast natts: %u", cur_oids.reloid, descr->tupdesc->natts, descr->toast->leafTupdesc->natts);

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
			TransactionId parentLogicalXid;

			memcpy(&parentSubid, ptr, sizeof(SubTransactionId));
			ptr += sizeof(SubTransactionId);
			memcpy(&logicalXid, ptr, sizeof(TransactionId));
			ptr += sizeof(TransactionId);
			memcpy(&parentLogicalXid, ptr, sizeof(TransactionId));
			ptr += sizeof(TransactionId);

			ReorderBufferAssignChild(ctx->reorder, parentLogicalXid, logicalXid, buf->origptr + (ptr - startPtr));

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

					if (ix_type == oIndexToast)
                                        {
						uint16 attnum;
						uint32 offset;
						uint32 old_chunk_size, /* without header */
						       new_chunk_size; /* without header */
						Pointer old_chunk;
						Pointer	new_chunk = NULL;
						HeapTuple toasttup;
						Datum  t_values[3];
						bool   t_isnull[3];
						bool   attnum_isnull, offset_isnull;
						int	pk_natts;
						bool need_to_free = false;
							
						Assert(o_toast_tupDesc);
						pk_natts = o_toast_tupDesc->natts - TOAST_LEAF_FIELDS_NUM;
						Assert(rec_flags & WAL_REC_TOAST);
						attnum = (uint16) o_fastgetattr(tuple.tuple, pk_natts + ATTN_POS, o_toast_tupDesc, &indexDescr->leafSpec, &attnum_isnull);
						offset = (uint32) o_fastgetattr(tuple.tuple, pk_natts + OFFSET_POS, o_toast_tupDesc, &indexDescr->leafSpec, &offset_isnull);
						Assert((!attnum_isnull) && (!offset_isnull));
						Assert(attnum > 0);
						/* Toast chunk in VARATT_4B uncompressed format */
						old_chunk = o_fastgetattr_ptr(tuple.tuple, pk_natts + DATA_POS, o_toast_tupDesc, &indexDescr->leafSpec);
						Assert(old_chunk && VARATT_IS_4B(old_chunk) && (!VARATT_IS_COMPRESSED(old_chunk)));
						old_chunk_size = VARSIZE(old_chunk) - VARHDRSZ;
						if (chunk_seq[attnum - 1] == 0)
						{
							int extra_header_size;

							if (VARATT_IS_4B(VARDATA(old_chunk)))
								extra_header_size = VARHDRSZ;
							else if (VARATT_IS_COMPRESSED(VARDATA(old_chunk)))
								extra_header_size = VARHDRSZ_COMPRESSED;
							else
								Assert(false);

							new_chunk_size = old_chunk_size - extra_header_size;
							need_to_free = true;
							new_chunk = palloc0(new_chunk_size + VARHDRSZ);
							memcpy(new_chunk, old_chunk, VARHDRSZ);
							SET_VARSIZE(new_chunk, new_chunk_size + VARHDRSZ);
							memcpy(VARDATA(new_chunk), VARDATA(old_chunk) + extra_header_size, new_chunk_size);
//							elog(INFO, "hdr: %u, extra hdr: %u",
//									VARSIZE(old_chunk),
//								       	VARSIZE(VARDATA(old_chunk)));
						}
						else
						{
							Assert(offset - VARHDRSZ == data_done[attnum - 1]);
							new_chunk = old_chunk;
							new_chunk_size = old_chunk_size;
						}

//						GetNewOidWithIndex(cur_oids.reloid, RelationGetRelid(toastidxs[validIndex], (AttrNumber) attnum);  
						t_values[0] = ObjectIdGetDatum(attnum + 8000);
						t_values[1] = Int32GetDatum(chunk_seq[attnum - 1]);
						t_values[2] = PointerGetDatum(new_chunk);
						t_isnull[0] = false;
						t_isnull[1] = false;
						t_isnull[2] = false;
						elog(INFO, "reloid: %u (attnum, seq, offset, oldsize, newsize): (%u, %u, %u, %u, %u) length_get: %u pk_natts: %u", cur_oids.reloid, attnum, chunk_seq[attnum - 1], offset, old_chunk_size, new_chunk_size, length, pk_natts);

//						if(chunk_seq[attnum - 1] == 0)
//							memcpy(&buf, ((char*)chunk)+8, 50);
//						else
//							memcpy(&buf, chunk+4, 50);
//						elog(INFO, "chunk_start %s", buf);

						Assert(heap_toast_tupDesc);
						toasttup = heap_form_tuple(heap_toast_tupDesc, t_values, t_isnull);
						change->data.tp.newtuple = record_buffer_tuple(ctx->reorder, toasttup, true);
						change->data.tp.clear_toast_afterwards = false;
						chunk_seq[attnum - 1]++;
#ifdef USE_ASSERT_CHECKING
						data_done[attnum - 1] += new_chunk_size;
#endif
						if(need_to_free && new_chunk)
						{
							pfree(new_chunk);
							need_to_free = false;
						}

	//					volatile bool a = 1;
//                                      while (a)
  //                                              {
    //                                            pg_usleep(1000L);
      //                                         }
                                        }
					else
					{
						int 		ixnum = PrimaryIndexNumber;

						Assert (!(rec_flags & WAL_REC_TOAST));
						Assert(ix_type != oIndexToast);
						/* Primary table contains TOASTed attributes needs conversion of them */
						if(descr->ntoastable > 0)
						{
							int 	     natts = descr->tupdesc->natts;
							Datum       *old_values = palloc0(natts * sizeof(Datum));
							Datum	    *new_values = palloc0(natts * sizeof(Datum));
							bool 	    *isnull = palloc0(natts * sizeof(bool));
							int         ctid_off = indexDescr->primaryIsCtid ? 1 : 0;
							HeapTuple   newheaptuple;

							elog(INFO, "%s", tuple.tuple.formatFlags & O_TUPLE_FLAGS_FIXED_FORMAT ? "FIXED":"NON_FIXED");
							Assert(descr->toast);
							for (int i = 0; i < natts; i++)
							{
								old_values[i] = o_fastgetattr(tuple.tuple, i + 1, descr->tupdesc, &indexDescr->leafSpec, &isnull[i]);
								Assert(!isnull[i]);
								new_values[i] = old_values[i];
							}

							/* Convert TOAST pointers */
							for (int i = 0; i < descr->ntoastable; i++)
							{
								int toast_attn = descr->toastable[i] - ctid_off;
								struct varlena *old_toastptr;
								struct varlena *new_toastptr;
								OToastValue otv;
								varatt_external ve;

								old_toastptr = (struct varlena *) DatumGetPointer(old_values[toast_attn]);
								Assert(VARATT_IS_EXTERNAL(old_toastptr));
								memcpy(&otv, old_toastptr, sizeof(otv));
								elog(INFO, "Old toast value: toast_attn: %u compression %u, raw_size, %u, toasted_size %u", toast_attn + 1, otv.compression, otv.raw_size, otv.toasted_size);
								ve.va_rawsize = otv.toasted_size;
								ve.va_extinfo = (otv.raw_size) | (otv.compression << VARLENA_EXTSIZE_BITS);
								ve.va_toastrelid = descr->toast->oids.reloid;
							        ve.va_valueid = ObjectIdGetDatum(toast_attn + 1 + 8000);
								Assert(data_done[toast_attn] == VARATT_EXTERNAL_GET_EXTSIZE(ve));
								Assert(!VARATT_EXTERNAL_IS_COMPRESSED(ve));
								elog(INFO, "New toast pointer compression: %u rawsize: %u, extinfo_size: %u, toastrelid %u, valueid %u  ", (ve.va_extinfo >> VARLENA_EXTSIZE_BITS), ve.va_rawsize,
									(ve.va_extinfo & VARLENA_EXTSIZE_MASK),
								       	ve.va_toastrelid, ve.va_valueid);
							
								new_toastptr = palloc0(TOAST_POINTER_SIZE);
								SET_VARTAG_EXTERNAL(new_toastptr, VARTAG_ONDISK);
								memcpy(VARDATA_EXTERNAL(new_toastptr), &ve, sizeof(ve));
								new_values[toast_attn] = PointerGetDatum(new_toastptr);

//						volatile bool a = 1;
//						while (a)
  //                                             {
    //                                            pg_usleep(1000L);
//						}

							}
							newheaptuple = heap_form_tuple(descr->tupdesc, new_values, isnull);
							change->data.tp.newtuple = record_buffer_tuple(ctx->reorder, newheaptuple, true);
							/* We're done with all chunks of TOAST rel, so reset chunk counters */
							if (chunk_seq)
								memset(chunk_seq, 0, sizeof(uint32) * descr->tupdesc->natts);
#ifdef USE_ASSERT_CHECKING
							if (data_done)
								memset(data_done, 0, sizeof(uint32) * descr->tupdesc->natts);
#endif
						}
						else /* Tuple without TOASTed attrs ptrs */
						{
							tts_orioledb_store_tuple(descr->newTuple, tuple.tuple,
											 descr, COMMITSEQNO_INPROGRESS,
											 ixnum, false,
											 NULL);
							change->data.tp.newtuple = record_buffer_tuple_slot(ctx->reorder, descr->newTuple);
						}
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
