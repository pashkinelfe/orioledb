/*-------------------------------------------------------------------------
 *
 * indices.h
 *		Indices routines.
 *
 * Copyright (c) 2021-2022, Oriole DB Inc.
 *
 * IDENTIFICATION
 *	  contrib/orioledb/include/catalog/indices.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef __INDICES_H__
#define __INDICES_H__

#include "postgres.h"

#include "orioledb.h"

#include "catalog/o_tables.h"
#include "tableam/descr.h"

#define recovery_first_worker 	 (0)
#define recovery_last_worker 	 (recovery_pool_size_guc - 1)
#define recovery_workers		 (recovery_pool_size_guc)
#define index_build_leader 		 (recovery_pool_size_guc)
#define index_build_first_worker (recovery_pool_size_guc + 1)
#define index_build_last_worker  (recovery_pool_size_guc + recovery_idx_pool_size_guc - 1)
#define index_build_workers 	 (recovery_idx_pool_size_guc - 1)
typedef struct BgWorkerHandle
{
	int			slot;
	uint64		generation;
} BgWorkerHandle;

typedef struct ODefineIndexContext
{
	Oid			oldNode;
} ODefineIndexContext;

/*
 * Status record for spooling/sorting phase.
 */
typedef struct oIdxSpool
{
	Tuplesortstate **sortstates;	/* state data for tuplesort.c */
	Relation	index;
	OTable 	 	*o_table;
	OTableDescr *descr;
	bool		isunique;

} oIdxSpool;

/*
 * Status for index builds performed in parallel. This is allocated in a
 * dynamic shared memory segment or recovery workers shared memory pool.
 * Note that there is a separate tuplesort TOC entry, private to tuplesort.c
 * but allocated by this module on its behalf.
 */
typedef struct oIdxShared
{
	/*
	 * These fields are not modified during the sort.  They primarily exist
	 * for the benefit of worker processes that need to create oIdxSpool state
	 * corresponding to that used by the leader.
	 */
	bool		isunique;
	bool		isconcurrent;
	int			scantuplesortstates;
	int 		nrecoveryworkers;
	/*
	 * workersdonecv is used to monitor the progress of workers.  All parallel
	 * participants must indicate that they are done before leader can use
	 * mutable state that workers maintain during scan (and before leader can
	 * proceed to tuplesort_performsort()).
	 */
	ConditionVariable workersdonecv;

	ConditionVariable recoverycv;
	/* Don't start next index build in recovery while current is in progress */
	bool recoveryidxbuild;
	/* Exclude relation with index being built in recovery from applying recovery modify messages
	 * concurrently */
	bool recoveryidxbuild_modify;
	ORelOids	oids;

	/*
	 * mutex protects all fields before heapdesc.
	 *
	 * These fields contain status information of interest to B-Tree index
	 * builds that must work just the same when an index is built in parallel.
	 */
	slock_t		mutex;

	/*
	 * Mutable state that is maintained by workers, and reported back to
	 * leader at end of parallel scan.
	 *
	 * nparticipantsdone is number of worker processes finished.
	 *
	 * reltuples is the total number of input heap tuples.
	 *
	 * indtuples is the total number of tuples that made it into the index.
	 */
	int			nparticipantsdone;
	int 		nrecoveryworkersjoined;

	double		reltuples;
	double		indtuples[INDEX_MAX_KEYS];

	/* Oriole-specific */
	void       (*worker_heap_sort_fn) (oIdxSpool *, void *, Sharedsort *, int sortmem, bool progress);
	ParallelOScanDescData poscan;
	OIndexNumber   ix_num;
	BgWorkerHandle *worker_handle;
	Size 		   o_table_size;
	char 		   o_table_serialized[];
} oIdxShared;

extern oIdxShared *recovery_oidxshared;
extern Sharedsort *recovery_sharedsort;

extern void o_define_index_validate(Relation rel, IndexStmt *stmt,
									bool skip_build,
									ODefineIndexContext **arg);
extern void o_define_index(Relation rel, Oid indoid, bool reindex,
						   bool skip_constraint_checks, bool skip_build,
						   ODefineIndexContext *context);

extern void o_index_drop(Relation tbl, OIndexNumber ix_num);
extern OIndexNumber o_find_ix_num_by_name(OTableDescr *descr,
										  char *ix_name);
extern bool is_in_indexes_rebuild(void);

extern void rebuild_indices(OTable *old_o_table, OTableDescr *old_descr,
							OTable *o_table, OTableDescr *descr);
extern void assign_new_oids(OTable *oTable, Relation rel);
extern void recreate_o_table(OTable *old_o_table, OTable *o_table);
extern void build_secondary_index(OTable *o_table, OTableDescr *descr,
								  OIndexNumber ix_num, bool in_dedicated_recovery_worker);
extern void _o_index_parallel_build_main(dsm_segment *seg, shm_toc *toc);
extern void _o_index_parallel_build_inner(dsm_segment *seg, shm_toc *toc,
										  char *o_table_serialized, Size o_table_size);
extern Size _o_index_parallel_estimate_shared(Size o_table_size);
#endif							/* __INDICES_H__ */
