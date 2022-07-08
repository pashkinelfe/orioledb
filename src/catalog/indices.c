/*-------------------------------------------------------------------------
 *
 * indices.c
 *		Indices routines
 *
 * Copyright (c) 2021-2022, Oriole DB Inc.
 *
 * IDENTIFICATION
 *	  contrib/orioledb/src/catalog/indices.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "orioledb.h"

#include "btree/build.h"
#include "btree/io.h"
#include "btree/undo.h"
#include "checkpoint/checkpoint.h"
#include "catalog/indices.h"
#include "catalog/o_opclass.h"
#include "catalog/o_sys_cache.h"
#include "recovery/recovery.h"
#include "recovery/wal.h"
#include "tableam/descr.h"
#include "tableam/operations.h"
#include "transam/oxid.h"
#include "tuple/slot.h"
#include "tuple/sort.h"
#include "tuple/toast.h"
#include "utils/planner.h"

#include "access/genam.h"
#include "access/relation.h"
#include "access/table.h"
#include "catalog/heap.h"
#include "catalog/index.h"
#include "catalog/namespace.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/event_trigger.h"
#include "commands/tablecmds.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_utilcmd.h"
#include "pgstat.h"
#include "storage/predicate.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"
#include "utils/tuplesort.h"

bool		in_indexes_rebuild = false;

bool
is_in_indexes_rebuild(void)
{
	return in_indexes_rebuild;
}

void
assign_new_oids(OTable *oTable, Relation rel)
{
	Oid			heap_relid,
				toast_relid;
#if PG_VERSION_NUM >= 140000
	ReindexParams params;
#endif
	CheckTableForSerializableConflictIn(rel);

	toast_relid = rel->rd_rel->reltoastrelid;
	if (OidIsValid(toast_relid))
	{
		Relation	toastrel = relation_open(toast_relid,
											 AccessExclusiveLock);

		RelationSetNewRelfilenode(toastrel,
								  toastrel->rd_rel->relpersistence);
		table_close(toastrel, NoLock);
	}

	heap_relid = RelationGetRelid(rel);
#if PG_VERSION_NUM >= 140000
	params.options = 0;
	params.tablespaceOid = InvalidOid;
	reindex_relation(heap_relid, REINDEX_REL_PROCESS_TOAST, &params);
#else
	reindex_relation(heap_relid, REINDEX_REL_PROCESS_TOAST, 0);
#endif

	PG_TRY();
	{
		in_indexes_rebuild = true;
		RelationSetNewRelfilenode(rel, rel->rd_rel->relpersistence);
	}
	PG_CATCH();
	{
		in_indexes_rebuild = false;
		PG_RE_THROW();
	}
	PG_END_TRY();
	in_indexes_rebuild = false;
	o_table_fill_oids(oTable, rel, &rel->rd_node);
	orioledb_free_rd_amcache(rel);
}

void
recreate_o_table(OTable *old_o_table, OTable *o_table)
{
	CommitSeqNo csn;
	OXid		oxid;
	int			oldTreeOidsNum,
				newTreeOidsNum;
	ORelOids	oldOids = old_o_table->oids,
			   *oldTreeOids,
				newOids = o_table->oids,
			   *newTreeOids;

	fill_current_oxid_csn(&oxid, &csn);

	oldTreeOids = o_table_make_index_oids(old_o_table, &oldTreeOidsNum);
	newTreeOids = o_table_make_index_oids(o_table, &newTreeOidsNum);

	o_tables_drop_by_oids(old_o_table->oids, oxid, csn);
	o_tables_add(o_table, oxid, csn);
	add_invalidate_wal_record(o_table->oids, old_o_table->oids.relnode);

	add_undo_truncate_relnode(oldOids, oldTreeOids, oldTreeOidsNum,
							  newOids, newTreeOids, newTreeOidsNum);
	pfree(oldTreeOids);
	pfree(newTreeOids);
}

static void
o_validate_index_elements(OTable *o_table, OIndexNumber ix_num,
						  OIndexType type, List *index_elems,
						  Node *whereClause)
{
	ListCell   *field_cell;

	if (whereClause)
		o_validate_funcexpr(whereClause, " are supported in "
										 "orioledb index predicate");

	foreach(field_cell, index_elems)
	{
		OTableField *field;
		IndexElem  *ielem = castNode(IndexElem, lfirst(field_cell));

		if (!ielem->expr)
		{
			int			attnum = o_table_fieldnum(o_table, ielem->name);

			if (attnum == o_table->nfields)
			{
				elog(ERROR, "indexed field %s is not found in orioledb table",
					 ielem->name);
			}
			field = &o_table->fields[attnum];

			if (type == oIndexPrimary && !field->notnull)
			{
				elog(ERROR, "primary key should include only NOT NULL columns, "
					 "but column %s is nullable", ielem->name);
			}

			if (type_is_collatable(field->typid))
			{
				if (!OidIsValid(field->collation))
					ereport(ERROR,
							(errcode(ERRCODE_INDETERMINATE_COLLATION),
							 errmsg("could not determine which collation to use for index expression"),
							 errhint("Use the COLLATE clause to set the collation explicitly.")));
			}
			else
			{
				if (OidIsValid(field->collation))
					ereport(ERROR,
							(errcode(ERRCODE_DATATYPE_MISMATCH),
							 errmsg("collations are not supported by type %s",
									format_type_be(field->typid))));
			}
		}
		else
		{
			o_validate_funcexpr(ielem->expr, " are supported in "
											 "orioledb index expressions");
		}
	}
}

void
o_index_create(Relation rel,
			   IndexStmt *stmt,
			   const char *queryString,
			   Node *utilityStmt)
{
	int			nattrs;
	Oid			myrelid = RelationGetRelid(rel);
	ORelOids	oids = {MyDatabaseId, myrelid, rel->rd_node.relNode};
	Oid			relid;
	OIndexNumber ix_num;
	OCompress	compress = InvalidOCompress;
	OIndexType	ix_type;
	OTable	   *old_o_table = NULL;
	OTable	   *o_table;
	Relation	index_rel;
	ObjectAddress address;
	bool		is_build;
	ORelOids	primary_oids;
	OTableDescr *old_descr = NULL;
	List	   *index_expr_fields = NIL;
	List	   *index_predicate = NIL;

	if (strcmp(stmt->accessMethod, "btree") != 0)
		ereport(ERROR, errmsg("'%s' access method is not supported",
							  stmt->accessMethod),
				errhint("Only 'btree' access method supported now "
						"for indices on orioledb tables."));

	/*
	 * TODO: ? if (strcmp(stmt->accessMethod, "orioledb") != 0) elog(ERROR,
	 * "Index should have 'orioledb' access method.");
	 */

	if (stmt->concurrent)
		elog(ERROR, "concurrent indexes are not supported.");

	if (stmt->tableSpace != NULL)
		elog(ERROR, "tablespaces aren't supported");

	stmt->options = extract_compress_rel_option(stmt->options,
												"compress",
												&compress);
	validate_compress(compress, "Index");

	if (stmt->options != NIL)
		elog(ERROR, "orioledb tables indices support "
			 "only \"compress\" option.");

	if (stmt->indexIncludingParams != NIL)
		elog(ERROR, "include indexes are not supported");

	relid = RangeVarGetRelidExtended(stmt->relation, AccessExclusiveLock,
									 0,
									 RangeVarCallbackOwnsRelation,
									 NULL);

	o_table = o_tables_get(oids);
	if (o_table == NULL)
	{
		elog(FATAL, "orioledb table does not exists for oids = %u, %u, %u",
			 (unsigned) oids.datoid, (unsigned) oids.reloid, (unsigned) oids.relnode);
	}

	/* check index type */
	if (stmt->primary)
		ix_type = oIndexPrimary;
	else if (stmt->unique)
		ix_type = oIndexUnique;
	else
		ix_type = oIndexRegular;

	/* check index fields number */
	nattrs = list_length(stmt->indexParams);
	if (ix_type == oIndexPrimary)
	{
		if (o_table->nindices > 0)
		{
			int			nattrs_max = 0,
						ix;

			if (o_table->has_primary)
				elog(ERROR, "table already has primary index");

			for (ix = 0; ix < o_table->nindices; ix++)
				nattrs_max = Max(nattrs_max, o_table->indices[ix].nfields);

			if (nattrs_max + nattrs > INDEX_MAX_KEYS)
			{
				elog(ERROR, "too many fields in the primary index for exiting indices");
			}
		}
	}
	else
	{
		if (o_table->nindices > 0
			&& o_table->indices[0].type != oIndexRegular
			&& nattrs + o_table->indices[0].nfields > INDEX_MAX_KEYS)
		{
			elog(ERROR, "too many fields in the index");
		}
	}

	primary_oids = ix_type == oIndexPrimary || !o_table->has_primary ?
		o_table->oids :
		o_table->indices[PrimaryIndexNumber].oids;
	is_build = tbl_data_exists(&primary_oids);

	/* Rebuild, assign new oids */
	if (ix_type == oIndexPrimary)
	{
		old_o_table = o_table;
		o_table = o_tables_get(oids);
		assign_new_oids(o_table, rel);
		oids = o_table->oids;
	}

	if (ix_type == oIndexPrimary)
	{
		ix_num = 0;				/* place first */
		o_table->has_primary = true;
		o_table->primary_init_nfields = o_table->nfields;
	}
	else
	{
		ix_num = o_table->nindices;
	}

	o_table->indices = (OTableIndex *) repalloc(o_table->indices,
												sizeof(OTableIndex) * (o_table->nindices + 1));

	/* move indices if needed */
	if (ix_type == oIndexPrimary && o_table->nindices > 0)
	{
		memmove(&o_table->indices[1],
				&o_table->indices[0],
				o_table->nindices * (sizeof(OTableIndex)));
	}
	o_table->nindices++;

	memset(&o_table->indices[ix_num],
		   0,
		   sizeof(OTableIndex));

	o_table->indices[ix_num].type = ix_type;
	o_table->indices[ix_num].nfields = list_length(stmt->indexParams);

	if (OCompressIsValid(compress))
		o_table->indices[ix_num].compress = compress;
	else if (ix_type == oIndexPrimary)
		o_table->indices[ix_num].compress = o_table->primary_compress;
	else
		o_table->indices[ix_num].compress = o_table->default_compress;

	/*
	 * Add primary key fields, because otherwise, when planning a query with a
	 * where clause consisting only of index fields and primary key fields, an
	 * index-only scan is not selected.
	 */
	if (ix_type != oIndexPrimary)
	{
		int			i;
		int			nfields;

		/* Remove assert if INCLUDE supported */
		Assert(!stmt->indexIncludingParams);

		if (o_table->has_primary)
		{
			nfields = o_table->indices[PrimaryIndexNumber].nfields;

			for (i = 0; i < nfields; i++)
			{
				OTableIndexField *field =
				&o_table->indices[PrimaryIndexNumber].fields[i];
				OTableField *table_field = &o_table->fields[field->attnum];
				IndexElem  *iparam = makeNode(IndexElem);

				iparam->name = pstrdup(table_field->name.data);
				iparam->expr = NULL;
				iparam->indexcolname = NULL;
				iparam->collation = NIL;
				iparam->opclass = NIL;
				iparam->opclassopts = NIL;
				stmt->indexIncludingParams =
					lappend(stmt->indexIncludingParams, iparam);
			}
		}
	}

	/* define index */
	stmt = transformIndexStmt(relid, stmt, queryString);

	if (stmt->idxname == NULL)
	{
		List	   *indexColNames = ChooseIndexColumnNames(stmt->indexParams);

		stmt->idxname = ChooseIndexName(RelationGetRelationName(rel),
										RelationGetNamespace(rel),
										indexColNames,
										stmt->excludeOpNames,
										stmt->primary,
										stmt->isconstraint);
	}

	/* check index fields */
	o_validate_index_elements(o_table, ix_num, ix_type, stmt->indexParams,
							  stmt->whereClause);
	EventTriggerAlterTableStart(utilityStmt);
	address =
		DefineIndex(relid,		/* OID of heap relation */
					stmt,
					InvalidOid, /* no predefined OID */
					InvalidOid, /* no parent index */
					InvalidOid, /* no parent constraint */
					false,		/* is_alter_table */
					true,		/* check_rights */
					false,		/* check_not_in_use */
					false,		/* skip_build */
					false);		/* quiet */

	/*
	 * Add the CREATE INDEX node itself to stash right away; if there were any
	 * commands stashed in the ALTER TABLE code, we need them to appear after
	 * this one.
	 */
	EventTriggerCollectSimpleCommand(address,
									 InvalidObjectAddress,
									 utilityStmt);
	EventTriggerAlterTableEnd();

	index_rel = index_open(address.objectId, AccessShareLock);
	memcpy(&o_table->indices[ix_num].name,
		   &index_rel->rd_rel->relname,
		   sizeof(NameData));
	o_table->indices[ix_num].oids.relnode = index_rel->rd_rel->relfilenode;

	index_expr_fields = RelationGetIndexExpressions(index_rel);
	index_predicate = RelationGetIndexPredicate(index_rel);
	/* fill index fields */
	o_table_fill_index(o_table, ix_num, ix_type, stmt->indexParams,
					   index_expr_fields, index_predicate);

	index_close(index_rel, AccessShareLock);

	o_table->indices[ix_num].oids.datoid = MyDatabaseId;
	o_table->indices[ix_num].oids.reloid = address.objectId;

	o_opclass_add_all(o_table);
	custom_types_add_all(o_table, &o_table->indices[ix_num]);

	/* update o_table */
	if (old_o_table)
		old_descr = o_fetch_table_descr(old_o_table->oids);

	/* create orioledb index from exist data */
	if (is_build)
	{
		OTableDescr tmpDescr;

		if (ix_type == oIndexPrimary)
		{
			Assert(old_o_table);
			o_fill_tmp_table_descr(&tmpDescr, o_table);
			rebuild_indices(old_o_table, old_descr,
							o_table, &tmpDescr);
			o_free_tmp_table_descr(&tmpDescr);
		}
		else
		{
			o_fill_tmp_table_descr(&tmpDescr, o_table);
			build_secondary_index(o_table, &tmpDescr, ix_num);
			o_free_tmp_table_descr(&tmpDescr);
		}
	}

	if (ix_type == oIndexPrimary)
	{
		CommitSeqNo csn;
		OXid		oxid;

		Assert(old_o_table);
		fill_current_oxid_csn(&oxid, &csn);
		recreate_o_table(old_o_table, o_table);
	}
	else
	{
		CommitSeqNo csn;
		OXid		oxid;

		fill_current_oxid_csn(&oxid, &csn);
		o_tables_update(o_table, oxid, csn);
		add_undo_create_relnode(o_table->oids,
								&o_table->indices[ix_num].oids,
								1);
		recreate_table_descr_by_oids(oids);
	}

	o_table_free(o_table);

	if (is_build)
		LWLockRelease(&checkpoint_state->oTablesAddLock);
}

void
build_secondary_index(OTable *o_table, OTableDescr *descr, OIndexNumber ix_num)
{
	BTreeIterator *iter;
	OIndexDescr *primary,
			   *idx;
	Tuplesortstate *sortstate;
	TupleTableSlot *primarySlot;
	Relation	tableRelation,
				indexRelation = NULL;
	double		heap_tuples,
				index_tuples;
	uint64		ctid;
	CheckpointFileHeader fileHeader;

	idx = descr->indices[o_table->has_primary ? ix_num : ix_num + 1];

	primary = GET_PRIMARY(descr);

	o_btree_load_shmem(&primary->desc);

	if (!is_recovery_in_progress())
		indexRelation = index_open(idx->oids.reloid, AccessShareLock);
	sortstate = tuplesort_begin_orioledb_index(idx, work_mem, false, NULL);
	if (indexRelation)
		index_close(indexRelation, AccessShareLock);

	iter = o_btree_iterator_create(&primary->desc, NULL, BTreeKeyNone,
								   COMMITSEQNO_INPROGRESS, ForwardScanDirection);

	primarySlot = MakeSingleTupleTableSlot(descr->tupdesc, &TTSOpsOrioleDB);

	heap_tuples = 0;
	ctid = 1;
	while (true)
	{
		OTuple		primaryTup;
		OTuple		secondaryTup;
		MemoryContext oldContext;

		primaryTup = o_btree_iterator_fetch(iter, NULL, NULL,
											BTreeKeyNone, true, NULL);

		if (O_TUPLE_IS_NULL(primaryTup))
			break;

		tts_orioledb_store_tuple(primarySlot, primaryTup, descr,
								 COMMITSEQNO_INPROGRESS, PrimaryIndexNumber,
								 true, NULL);

		slot_getallattrs(primarySlot);

		heap_tuples++;

		oldContext = MemoryContextSwitchTo(sortstate->tuplecontext);
		secondaryTup = tts_orioledb_make_secondary_tuple(primarySlot, idx, true);
		MemoryContextSwitchTo(oldContext);

		o_btree_check_size_of_tuple(o_tuple_size(secondaryTup, &idx->leafSpec), idx->name.data, true);
		tuplesort_putotuple(sortstate, secondaryTup);

		ExecClearTuple(primarySlot);
	}
	index_tuples = heap_tuples;
	ExecDropSingleTupleTableSlot(primarySlot);
	pfree(iter);

	tuplesort_performsort(sortstate);

	btree_write_index_data(&idx->desc, idx->leafTupdesc, sortstate,
						   ctid, &fileHeader);
	tuplesort_end_orioledb_index(sortstate);

	/*
	 * We hold oTablesAddLock till o_tables_update().  So, checkpoint number
	 * in the data file will be consistent with o_tables metadata.
	 */
	LWLockAcquire(&checkpoint_state->oTablesAddLock, LW_SHARED);

	btree_write_file_header(&idx->desc, &fileHeader);

	if (!is_recovery_in_progress())
	{
		tableRelation = table_open(o_table->oids.reloid, AccessExclusiveLock);
		indexRelation = index_open(o_table->indices[ix_num].oids.reloid,
								   AccessExclusiveLock);
		index_update_stats(tableRelation,
						   true,
						   heap_tuples);

		index_update_stats(indexRelation,
						   false,
						   index_tuples);

		/* Make the updated catalog row versions visible */
		CommandCounterIncrement();
		table_close(tableRelation, AccessExclusiveLock);
		index_close(indexRelation, AccessExclusiveLock);
	}
}

void
rebuild_indices(OTable *old_o_table, OTableDescr *old_descr,
				OTable *o_table, OTableDescr *descr)
{
	BTreeIterator *iter;
	OIndexDescr *primary,
			   *idx;
	Tuplesortstate **sortstates;
	Tuplesortstate *toastSortState;
	TupleTableSlot *primarySlot;
	int			i;
	Relation	tableRelation;
	double		heap_tuples,
				index_tuples;
	uint64		ctid;
	CheckpointFileHeader *fileHeaders;
	CheckpointFileHeader toastFileHeader;

	primary = GET_PRIMARY(old_descr);
	o_btree_load_shmem(&primary->desc);

	sortstates = (Tuplesortstate **) palloc(sizeof(Tuplesortstate *) *
											descr->nIndices);
	fileHeaders = (CheckpointFileHeader *) palloc(sizeof(CheckpointFileHeader) *
												  descr->nIndices);

	for (i = 0; i < descr->nIndices; i++)
	{
		idx = descr->indices[i];
		sortstates[i] = tuplesort_begin_orioledb_index(idx, work_mem, false, NULL);
	}
	primarySlot = MakeSingleTupleTableSlot(old_descr->tupdesc, &TTSOpsOrioleDB);

	btree_open_smgr(&descr->toast->desc);
	toastSortState = tuplesort_begin_orioledb_toast(descr->toast,
													descr->indices[0],
													work_mem, false, NULL);

	iter = o_btree_iterator_create(&primary->desc, NULL, BTreeKeyNone,
								   COMMITSEQNO_INPROGRESS, ForwardScanDirection);
	heap_tuples = 0;
	ctid = 0;
	while (true)
	{
		OTuple		primaryTup;

		primaryTup = o_btree_iterator_fetch(iter, NULL, NULL,
											BTreeKeyNone, true, NULL);

		if (O_TUPLE_IS_NULL(primaryTup))
			break;

		tts_orioledb_store_tuple(primarySlot, primaryTup, old_descr,
								 COMMITSEQNO_INPROGRESS, PrimaryIndexNumber,
								 true, NULL);

		slot_getallattrs(primarySlot);
		tts_orioledb_detoast(primarySlot);
		tts_orioledb_toast(primarySlot, descr);

		for (i = 0; i < descr->nIndices; i++)
		{
			OTuple		newTup;
			MemoryContext oldContext;

			idx = descr->indices[i];

			if (!o_is_index_predicate_satisfied(idx, primarySlot,
												idx->econtext))
				continue;

			oldContext = MemoryContextSwitchTo(sortstates[i]->tuplecontext);
			if (i == 0)
			{
				if (idx->primaryIsCtid)
				{
					primarySlot->tts_tid.ip_posid = (OffsetNumber) ctid;
					BlockIdSet(&primarySlot->tts_tid.ip_blkid, (uint32) (ctid >> 16));
					ctid++;
				}
				newTup = tts_orioledb_form_orphan_tuple(primarySlot, descr);
			}
			else
			{
				newTup = tts_orioledb_make_secondary_tuple(primarySlot, idx, true);
			}
			MemoryContextSwitchTo(oldContext);

			o_btree_check_size_of_tuple(o_tuple_size(newTup, &idx->leafSpec), idx->name.data, true);
			tuplesort_putotuple(sortstates[i], newTup);
		}

		tts_orioledb_toast_sort_add(primarySlot, descr, toastSortState);

		ExecClearTuple(primarySlot);
		heap_tuples++;
	}
	index_tuples = heap_tuples;

	ExecDropSingleTupleTableSlot(primarySlot);
	btree_iterator_free(iter);

	for (i = 0; i < descr->nIndices; i++)
	{
		idx = descr->indices[i];
		tuplesort_performsort(sortstates[i]);
		btree_write_index_data(&idx->desc, idx->leafTupdesc, sortstates[i],
							   (idx->primaryIsCtid && i == PrimaryIndexNumber) ? ctid : 0,
							   &fileHeaders[i]);
		tuplesort_end_orioledb_index(sortstates[i]);
	}
	pfree(sortstates);

	tuplesort_performsort(toastSortState);
	btree_write_index_data(&descr->toast->desc, descr->toast->leafTupdesc,
						   toastSortState, 0, &toastFileHeader);
	tuplesort_end_orioledb_index(toastSortState);

	/*
	 * We hold oTablesAddLock till o_tables_update().  So, checkpoint number
	 * in the data file will be consistent with o_tables metadata.
	 */
	LWLockAcquire(&checkpoint_state->oTablesAddLock, LW_SHARED);

	for (i = 0; i < descr->nIndices; i++)
		btree_write_file_header(&descr->indices[i]->desc, &fileHeaders[i]);
	btree_write_file_header(&descr->toast->desc, &toastFileHeader);

	pfree(fileHeaders);

	if (!is_recovery_in_progress())
	{
		tableRelation = table_open(o_table->oids.reloid, AccessExclusiveLock);
		index_update_stats(tableRelation,
						   true,
						   heap_tuples);

		for (i = 0; i < o_table->nindices; i++)
		{
			OTableIndex *table_index = &o_table->indices[i];
			int			ctid_off = o_table->has_primary ? 0 : 1;
			OIndexDescr *idx_descr = descr->indices[i + ctid_off];
			Relation	indexRelation =
			index_open(table_index->oids.reloid, AccessExclusiveLock);

			if (table_index->type != oIndexPrimary)
			{
				Oid			reloid = RelationGetRelid(indexRelation);
				Relation	pg_class;
				Relation	pg_index;
				Relation	pg_attribute;
				Form_pg_class class_form;
				Form_pg_index index_form;
				HeapTuple	class_tuple,
							index_tuple;

				pg_class = table_open(RelationRelationId, RowExclusiveLock);
				class_tuple = SearchSysCacheCopy1(RELOID,
												  ObjectIdGetDatum(reloid));
				if (!HeapTupleIsValid(class_tuple))
					elog(ERROR, "could not find pg_class for relation %u",
						 reloid);
				class_form = (Form_pg_class) GETSTRUCT(class_tuple);

				pg_index = table_open(IndexRelationId, RowExclusiveLock);
				index_tuple = SearchSysCacheCopy1(INDEXRELID,
												  ObjectIdGetDatum(reloid));
				if (!HeapTupleIsValid(index_tuple))
					elog(ERROR, "could not find pg_index for relation %u",
						 reloid);
				index_form = (Form_pg_index) GETSTRUCT(index_tuple);

				pg_attribute = table_open(AttributeRelationId, RowExclusiveLock);

				if (o_table->has_primary)
				{
					int2vector *indkey;
					int			attnum;
					int			pkey_natts;
					Datum		values[Natts_pg_index] = {0};
					bool		nulls[Natts_pg_index] = {0};
					bool		replaces[Natts_pg_index] = {0};
					HeapTuple	old_index_tuple;

					pkey_natts = idx_descr->nFields -
						idx_descr->nPrimaryFields;
					for (attnum = 0; attnum < pkey_natts; attnum++)
					{
						FormData_pg_attribute attribute;
#if PG_VERSION_NUM >= 140000
						FormData_pg_attribute *aattr[] = {&attribute};
						TupleDesc	tupdesc;
#endif
						OIndexField *idx_field = &idx_descr->fields[idx_descr->nPrimaryFields + attnum];
						OTableField *table_field = &o_table->fields[idx_field->tableAttnum - 1];

						attribute.attrelid = reloid;
						namestrcpy(&(attribute.attname), table_field->name.data);
						attribute.atttypid = table_field->typid;
						attribute.attstattarget = 0;
						attribute.attlen = table_field->typlen;
						attribute.attnum = idx_descr->nPrimaryFields + attnum + 1;
						attribute.attndims = table_field->ndims;
						attribute.atttypmod = table_field->typmod;
						attribute.attbyval = table_field->byval;
						attribute.attalign = table_field->align;
						attribute.attstorage = table_field->storage;
#if PG_VERSION_NUM >= 140000
						attribute.attcompression = '\0';
#endif
						attribute.attnotnull = table_field->notnull;
						attribute.atthasdef = false;
						attribute.atthasmissing = false;
						attribute.attidentity = '\0';
						attribute.attgenerated = '\0';
						attribute.attisdropped = false;
						attribute.attislocal = true;
						attribute.attinhcount = 0;
						attribute.attcollation = table_field->collation;

#if PG_VERSION_NUM >= 140000
						tupdesc = CreateTupleDesc(lengthof(aattr), (FormData_pg_attribute **) &aattr);
						InsertPgAttributeTuples(pg_attribute, tupdesc, reloid, NULL, NULL);
#else
						InsertPgAttributeTuple(pg_attribute, &attribute, (Datum) 0, NULL);
#endif
					}

					class_form->relnatts += pkey_natts;
					index_form->indnatts += pkey_natts;

					indkey = buildint2vector(NULL, index_form->indnatts);
					for (i = 0; i < index_form->indnkeyatts; i++)
						indkey->values[i] = index_form->indkey.values[i];
					for (i = 0; i < pkey_natts; i++)
					{
						int			j = index_form->indnkeyatts + i;
						OIndexField *idx_field =
						&idx_descr->fields[idx_descr->nPrimaryFields + i];

						indkey->values[j] = idx_field->tableAttnum;
					}

					replaces[Anum_pg_index_indkey - 1] = true;
					values[Anum_pg_index_indkey - 1] = PointerGetDatum(indkey);

					old_index_tuple = index_tuple;
					index_tuple = heap_modify_tuple(old_index_tuple,
													RelationGetDescr(pg_index), values,
													nulls, replaces);
					heap_freetuple(old_index_tuple);
				}
				else
				{
					int			attnum;
					int			pkey_natts;

					pkey_natts = index_form->indnatts -
						index_form->indnkeyatts;
					for (attnum = 0; attnum < pkey_natts; attnum++)
					{
						HeapTuple	attr_tuple;

						attr_tuple =
							SearchSysCacheCopy2(ATTNUM,
												ObjectIdGetDatum(reloid),
												Int16GetDatum(index_form->indnkeyatts + attnum + 1));

						if (!HeapTupleIsValid(attr_tuple))
							elog(ERROR, "could not find pg_attribute for "
								 "relation %u", reloid);

						CatalogTupleDelete(pg_attribute, &attr_tuple->t_self);
					}
					class_form->relnatts = index_form->indnkeyatts;
					index_form->indnatts = index_form->indnkeyatts;
				}

				CatalogTupleUpdate(pg_class, &class_tuple->t_self,
								   class_tuple);
				CatalogTupleUpdate(pg_index, &index_tuple->t_self,
								   index_tuple);
				heap_freetuple(class_tuple);
				heap_freetuple(index_tuple);
				table_close(pg_attribute, RowExclusiveLock);
				table_close(pg_class, RowExclusiveLock);
				table_close(pg_index, RowExclusiveLock);
			}

			index_update_stats(indexRelation, false, index_tuples);
			index_close(indexRelation, AccessExclusiveLock);
		}


		/* Make the updated catalog row versions visible */
		CommandCounterIncrement();
		table_close(tableRelation, AccessExclusiveLock);
	}
}

static void
drop_primary_index(Relation rel, OTable *o_table)
{
	OTable	   *old_o_table;
	OTableDescr tmp_descr;
	OTableDescr *old_descr;

	Assert(o_table->indices[PrimaryIndexNumber].type == oIndexPrimary);

	old_o_table = o_table;
	o_table = o_tables_get(o_table->oids);
	assign_new_oids(o_table, rel);

	memmove(&o_table->indices[0],
			&o_table->indices[1],
			(o_table->nindices - 1) * sizeof(OTableIndex));
	o_table->nindices--;
	o_table->has_primary = false;
	o_table->primary_init_nfields = o_table->nfields + 1;	/* + ctid field */

	old_descr = o_fetch_table_descr(old_o_table->oids);

	o_fill_tmp_table_descr(&tmp_descr, o_table);
	rebuild_indices(old_o_table, old_descr, o_table, &tmp_descr);
	o_free_tmp_table_descr(&tmp_descr);

	recreate_o_table(old_o_table, o_table);

	LWLockRelease(&checkpoint_state->oTablesAddLock);

}

static void
drop_secondary_index(OTable *o_table, OIndexNumber ix_num)
{
	CommitSeqNo csn;
	OXid		oxid;
	ORelOids	deletedOids;

	Assert(o_table->indices[ix_num].type != oIndexInvalid);

	deletedOids = o_table->indices[ix_num].oids;
	o_table->nindices--;
	if (o_table->nindices > 0)
	{
		memmove(&o_table->indices[ix_num],
				&o_table->indices[ix_num + 1],
				(o_table->nindices - ix_num) * sizeof(OTableIndex));
	}

	/* update o_table */
	fill_current_oxid_csn(&oxid, &csn);
	o_tables_update(o_table, oxid, csn);
	add_undo_drop_relnode(o_table->oids, &deletedOids, 1);
	recreate_table_descr_by_oids(o_table->oids);
}

void
o_index_drop(Relation tbl, OIndexNumber ix_num)
{
	ORelOids	oids = {MyDatabaseId, tbl->rd_rel->oid,
	tbl->rd_node.relNode};
	OTable	   *o_table;

	o_table = o_tables_get(oids);

	if (o_table == NULL)
	{
		elog(FATAL, "orioledb table does not exists for oids = %u, %u, %u",
			 (unsigned) oids.datoid, (unsigned) oids.reloid, (unsigned) oids.relnode);
	}

	if (o_table->indices[ix_num].type == oIndexPrimary)
		drop_primary_index(tbl, o_table);
	else
		drop_secondary_index(o_table, ix_num);
	o_table_free(o_table);

}

OIndexNumber
o_find_ix_num_by_name(OTableDescr *descr, char *ix_name)
{
	OIndexNumber result = InvalidIndexNumber;
	int			i;

	for (i = 0; i < descr->nIndices; i++)
	{
		if (strcmp(descr->indices[i]->name.data, ix_name) == 0)
		{
			result = i;
			break;
		}
	}
	return result;
}
