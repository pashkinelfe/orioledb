/*-------------------------------------------------------------------------
 *
 * o_tables.h
 * 		Routines for orioledb tables system tree.
 *
 * Copyright (c) 2021-2022, Oriole DB Inc.
 *
 * IDENTIFICATION
 *	  contrib/orioledb/include/catalog/o_tables.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef __O_TABLES_H__
#define __O_TABLES_H__

#include "btree/btree.h"
#include "catalog/sys_trees.h"

#include "access/tupdesc.h"
#include "access/tupdesc_details.h"
#include "executor/execExpr.h"
#include "catalog/objectaddress.h"
#include "nodes/parsenodes.h"

/*
 * Describes a field of an orioledb table.
 */
typedef struct
{
	NameData	name;
	Oid			typid;
	Oid			collation;
	int32		typmod BKI_DEFAULT(-1);
	int32		ndims;
	bool		byval;
	bool		droped;
	bool		notnull;
	int16		typlen;
	char		align;
	char		storage;
	bool		hasmissing;
	bool		hasdef;
} OTableField;

/*
 * Describes an index field of an orioledb table.
 */
typedef struct
{
	int			attnum;
	Oid			collation;
	Oid			opclass;
	SortByDir	ordering;
	SortByNulls nullsOrdering;
} OTableIndexField;

/*
 * Describes an index of an orioledb table.
 */
typedef struct
{
	NameData	name;
	ORelOids	oids;
	OIndexType	type;
	OCompress	compress;
	uint8		nfields;
	OTableIndexField fields[INDEX_MAX_KEYS];
	uint8		nexprfields;
	OTableField *exprfields;
	List	   *expressions;	/* list of Expr */
	char	   *predicate_str;
	List	   *predicate;		/* list of Expr */
	MemoryContext index_mctx;
} OTableIndex;

/*
 * Describes an orioledb table.
 */
typedef struct
{
	ORelOids	oids;
	ORelOids	toast_oids;
	OCompress	default_compress;
	OCompress	primary_compress;
	OCompress	toast_compress;
	uint16		nfields;
	uint16		primary_init_nfields;
	uint16		nindices;
	Oid			tid_btree_ops_oid;	/* have to store it here */
	bool		has_primary;
	bool		has_missing;
	bool		has_default;
	OTableIndex *indices;
	OTableField *fields;
	AttrMissing *missing;		/* missing attributes values, NULL if none */
	Expr	  **defvals;
	uint32		version;		/* not serialized in serialize_o_table */
} OTable;

extern void o_table_fill_index(OTable *o_table, OIndexNumber ix_num,
							   OIndexType type, List *index_elems,
							   List *index_expr_elems,
							   List *index_predicate);

/* Creates and fills OTable. */
extern OTable *o_table_tableam_create(ORelOids oids, ORelOids toastOids, TupleDesc tupdesc,
									  OCompress default_compress, OCompress primary_compress,
									  OCompress toast_compress);

OTableField *o_tables_get_builtin_field(Oid type);
extern void o_tables_tupdesc_init_builtin(TupleDesc desc, AttrNumber att_num,
										  char *name, Oid type);

extern TupleDesc o_table_fields_make_tupdesc(OTableField *fields, int nfields);

/* Returns tuple descriptor of the OTable */
extern TupleDesc o_table_tupdesc(OTable *o_table);

/* Finds table field by its name */
extern OTableField *o_table_field_by_name(OTable *table, const char *name);

/* Drops a table by oids from o_tables list */
extern OTable *o_tables_drop_by_oids(ORelOids oids, OXid oxid, CommitSeqNo csn);

/* Drops all tables from o_tables list */
extern void o_tables_drop_all(OXid oxid, CommitSeqNo csn, Oid database_id);

/* Drops all columns of a specific type */
extern void o_tables_drop_columns_by_type(OXid oxid, CommitSeqNo csn, Oid type_oid);

/* Adds a new table to o_tables list */
extern bool o_tables_add(OTable *table, OXid oxid, CommitSeqNo csn);

/* Returns OTable by its oids */
extern OTable *o_tables_get(ORelOids oids);

/* Returns OTable by its oids and version */
extern OTable *o_tables_get_by_oids_and_version(ORelOids oids, uint32 *version);

/* Returns OTable by its index oids */
extern OTable *o_tables_get_by_tree(ORelOids oids, OIndexType type);

/* Updates OTable description in o_tables list */
extern bool o_tables_update(OTable *table, OXid oxid, CommitSeqNo csn);

/* Same o_tables_update, but it also writes old_relnode to WAL */
extern bool o_tables_update_on_rebuild(OTable *table, OXid oxid,
									   CommitSeqNo csn, Oid old_relnode);

/* Checks tuple descriptor for compatibility with orioledb module */
extern void o_tables_validate_tupdesc(TupleDesc tupdesc);

/* Free memory of OTable struct */
extern void o_table_free(OTable *table);

extern ORelOids *o_table_make_index_oids(OTable *table, int *num);

/* callback for o_tables_foreach() */
typedef void (*OTablesCallback) (OTable *descr, void *arg);

/* callback for o_tables_foreach_oids() */
typedef void (*OTablesOidsCallback) (ORelOids oids, void *arg);

/* Iterates through o_tables list. */
extern void o_tables_foreach(OTablesCallback callback,
							 CommitSeqNo csn,
							 void *arg);
extern void o_tables_foreach_oids(OTablesOidsCallback callback,
								  CommitSeqNo csn,
								  void *arg);

/*
 * We can't use relation_open/LockRelationId locks to protect relations that
 * belong to other database.
 *
 * We must use this locks to protect critical code sections interacting with
 * relations from other databases (workers code, walk_page() for backends).
 *
 * Foreign-data wrapper handler functions are already protected
 * by top-level, there are no need on this locks nested TableAm handler functions.
 */
extern bool o_tables_rel_try_lock_extended(ORelOids *oids, int lockmode, bool *nested, bool checkpoint);
extern void o_tables_rel_lock_extended(ORelOids *oids, int lockmode, bool checkpoint);
extern void o_tables_rel_unlock_extended(ORelOids *oids, int lockmode, bool checkpoint);

/* Deserialize OTable stored in O_TABLES sys tree */
extern void o_serialize_node(Node *node, StringInfo str);
extern Node *o_deserialize_node(Pointer *ptr);
extern void o_serialize_string(char *serialized, StringInfo str);
extern char *o_deserialize_string(Pointer *ptr);

static inline bool
o_tables_rel_try_lock(ORelOids *oids, int lockmode, bool *nested)
{
	return o_tables_rel_try_lock_extended(oids, lockmode, nested, false);
}

static inline void
o_tables_rel_lock(ORelOids *oids, int lockmode)
{
	o_tables_rel_lock_extended(oids, lockmode, false);
}

static inline void
o_tables_rel_unlock(ORelOids *oids, int lockmode)
{
	o_tables_rel_unlock_extended(oids, lockmode, false);
}

extern void o_table_fill_oids(OTable *oTable, Relation rel,
							  const RelFileNode *newrnode);

extern void o_table_fill_constr(OTable *o_table, int i,
								AttrMissing *attrmiss, Expr *defval);
extern void o_tupdesc_load_constr(TupleDesc tupdesc,
								  OTable *o_table);
extern char *o_get_type_name(Oid typid, int32 typmod);
extern char *o_get_collation_name(Oid colid);

static inline int
o_table_fieldnum(OTable *table, const char *name)
{
	int			i;

	for (i = 0; i < table->nfields; i++)
	{
		if (table->fields[i].droped)
			continue;
		if (pg_strcasecmp(NameStr(table->fields[i].name), name) == 0)
			return i;
	}
	return i;
}

extern bool OExecInitFuncHook(ExprEvalStep *scratch, Expr *node, List *args,
							  Oid funcid, Oid inputcollid, ExprState *state);

extern bool o_func_hook_enabled;

#endif							/* __O_TABLES_H__ */
