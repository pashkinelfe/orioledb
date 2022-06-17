/*-------------------------------------------------------------------------
 *
 * o_tables.c
 * 		Routines for query processing.
 *
 * Copyright (c) 2021-2022, Oriole DB Inc.
 *
 * IDENTIFICATION
 *	  contrib/orioledb/src/utils/planner.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "orioledb.h"

#include "utils/planner.h"

#include "catalog/pg_proc.h"
#include "executor/functions.h"
#include "funcapi.h"
#include "nodes/nodeFuncs.h"
#include "parser/analyze.h"
#include "tcop/tcopprot.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/syscache.h"

typedef struct
{
	char	   *proname;
	char	   *prosrc;
} inline_error_callback_arg;

/*
 * error context callback to let us supply a call-stack traceback
 */
static void
sql_validate_error_callback(void *arg)
{
	inline_error_callback_arg *callback_arg = (inline_error_callback_arg *) arg;
	int			syntaxerrposition;

	/* If it's a syntax error, convert to internal syntax error report */
	syntaxerrposition = geterrposition();
	if (syntaxerrposition > 0)
	{
		errposition(0);
		internalerrposition(syntaxerrposition);
		internalerrquery(callback_arg->prosrc);
	}

	errcontext("SQL function \"%s\" during body validation",
			   callback_arg->proname);
}

void
o_process_sql_function(HeapTuple	procedureTuple, bool (*walker) (),
					   void *context, Oid functionId, Oid inputcollid,
					   List *args)
{
	Form_pg_proc				procedureStruct;
	MemoryContext				mycxt,
								oldcxt;
	ErrorContextCallback		sqlerrcontext;
	inline_error_callback_arg	callback_arg;
	Datum						proc_body;
	FuncExpr				   *fexpr;
	bool						isNull;
	Query					   *querytree;
	bool						has_body = true;

	procedureStruct = (Form_pg_proc) GETSTRUCT(procedureTuple);

	/*
		* Make a temporary memory context, so that we don't leak all the
		* stuff that parsing might create.
		*/
	mycxt = AllocSetContextCreate(CurrentMemoryContext,
								  "inline_function",
								  ALLOCSET_DEFAULT_SIZES);
	oldcxt = MemoryContextSwitchTo(mycxt);

	/*
		* Setup error traceback support for ereport().
		* This is so that we can finger the function that
		* bad information came from.
		*/
	callback_arg.proname = NameStr(procedureStruct->proname);

	/* Fetch the function body */
	proc_body = SysCacheGetAttr(PROCOID,
								procedureTuple,
								Anum_pg_proc_prosrc,
								&isNull);
	if (isNull)
		elog(ERROR, "null prosrc for function %u", functionId);
	callback_arg.prosrc = TextDatumGetCString(proc_body);

	sqlerrcontext.callback = sql_validate_error_callback;
	sqlerrcontext.arg = (void *) &callback_arg;
	sqlerrcontext.previous = error_context_stack;
	error_context_stack = &sqlerrcontext;

	/*
		* We need a dummy FuncExpr node containing the already-simplified
		* arguments.  (In some cases we don't really need it, but building
		* it is cheap enough that it's not worth contortions to avoid.)
		*/
	fexpr = makeNode(FuncExpr);
	fexpr->funcid = functionId;
	fexpr->funcresulttype = procedureStruct->prorettype;
	fexpr->funcretset = procedureStruct->proretset;
	fexpr->funcvariadic = procedureStruct->provariadic;
	fexpr->funcformat = COERCE_EXPLICIT_CALL; /* doesn't matter */
	fexpr->funccollid = InvalidOid;		  /* doesn't matter */
	fexpr->inputcollid = inputcollid;
	fexpr->args = args;
	fexpr->location = -1;

#if PG_VERSION_NUM >= 140000
	/* If we have prosqlbody, pay attention to that not prosrc */
	proc_body = SysCacheGetAttr(PROCOID,
								procedureTuple,
								Anum_pg_proc_prosqlbody,
								&isNull);
	if (!isNull)
	{
		Node *n;
		List *querytree_list;

		n = stringToNode(TextDatumGetCString(proc_body));
		if (IsA(n, List))
			querytree_list = linitial_node(List, castNode(List, n));
		else
			querytree_list = list_make1(n);
		has_body = list_length(querytree_list) == 1;
		if (has_body)
		{
			querytree = linitial(querytree_list);

			/*
				* Because we'll insist below that the querytree have an empty rtable
				* and no sublinks, it cannot have any relation references that need
				* to be locked or rewritten.  So we can omit those steps.
				*/
		}
	}
	else
	{
#endif
		SQLFunctionParseInfoPtr	pinfo;
		List				   *raw_parsetree_list;

		/* Set up to handle parameters while parsing the function body. */
		pinfo = prepare_sql_fn_parse_info(procedureTuple,
										  (Node *) fexpr,
										  inputcollid);

		/*
			* We just do parsing and parse analysis, not rewriting, because
			* rewriting will not affect table-free-SELECT-only queries, which is
			* all that we care about.  Also, we can punt as soon as we detect
			* more than one command in the function body.
			*/
		raw_parsetree_list = pg_parse_query(callback_arg.prosrc);
		has_body = list_length(raw_parsetree_list) == 1;
		if (has_body)
		{
			ParseState *pstate = make_parsestate(NULL);
			pstate->p_sourcetext = callback_arg.prosrc;
			sql_fn_parser_setup(pstate, pinfo);

			querytree = transformTopLevelStmt(pstate, linitial(raw_parsetree_list));

			free_parsestate(pstate);
		}
#if PG_VERSION_NUM >= 140000
	}
#endif

	/*
		* The single command must be a simple "SELECT expression".
		*
		* Note: if you change the tests involved in this, see also plpgsql's
		* exec_simple_check_plan().  That generally needs to have the same idea
		* of what's a "simple expression", so that inlining a function that
		* previously wasn't inlined won't change plpgsql's conclusion.
		*/
	if (has_body &&
		IsA(querytree, Query) &&
		querytree->commandType == CMD_SELECT &&
		!querytree->hasAggs &&
		!querytree->hasWindowFuncs &&
		!querytree->hasTargetSRFs &&
		!querytree->hasSubLinks &&
		!querytree->cteList &&
		!querytree->rtable &&
		!querytree->jointree->fromlist &&
		!querytree->jointree->quals &&
		!querytree->groupClause &&
		!querytree->groupingSets &&
		!querytree->havingQual &&
		!querytree->windowClause &&
		!querytree->distinctClause &&
		!querytree->sortClause &&
		!querytree->limitOffset &&
		!querytree->limitCount &&
		!querytree->setOperations &&
		list_length(querytree->targetList) == 1)
	{
		TupleDesc	rettupdesc;
		List	   *querytree_list;

		/* If the function result is composite, resolve it */
		(void) get_expr_result_type((Node *)fexpr,
									NULL,
									&rettupdesc);

		/*
			* Make sure the function (still) returns what it's declared to.  This
			* will raise an error if wrong, but that's okay since the function would
			* fail at runtime anyway.  Note that check_sql_fn_retval will also insert
			* a coercion if needed to make the tlist expression match the declared
			* type of the function.
			*
			* Note: we do not try this until we have verified that no rewriting was
			* needed; that's probably not important, but let's be careful.
			*/
		querytree_list = list_make1(querytree);
		if (!check_sql_fn_retval(list_make1(querytree_list),
									procedureStruct->prorettype,
									rettupdesc, false, NULL))
		{
			/*
				* Given the tests above, check_sql_fn_retval shouldn't have decided to
				* inject a projection step, but let's just make sure.
				*/
			if (querytree == linitial(querytree_list))

			{
				Node	   *newexpr;
				/* Now we can grab the tlist expression */
				newexpr = (Node *)((TargetEntry *)linitial(querytree->targetList))->expr;

				/*
					* If the SQL function returns VOID, we can only inline it if it is a
					* SELECT of an expression returning VOID (ie, it's just a redirection to
					* another VOID-returning function).  In all non-VOID-returning cases,
					* check_sql_fn_retval should ensure that newexpr returns the function's
					* declared result type, so this test shouldn't fail otherwise; but we may
					* as well cope gracefully if it does.
					*/
				if (exprType(newexpr) == procedureStruct->prorettype)

				{
					MemoryContextSwitchTo(oldcxt);
					expression_tree_walker(o_wrap_top_funcexpr(newexpr),
										   walker, context);
					MemoryContextSwitchTo(mycxt);
				}
			}
		} /* reject whole-tuple-result cases */
	}

	MemoryContextSwitchTo(oldcxt);
	MemoryContextDelete(mycxt);
	error_context_stack = sqlerrcontext.previous;
}

Node *
o_wrap_top_funcexpr(Node *node)
{
	static NamedArgExpr named_arg = {.xpr = {.type = T_NamedArgExpr}};

	switch (node->type)
	{
		case T_FuncExpr:
			named_arg.arg = (Expr *) node;
			return (Node *) &named_arg;
		default:
			return node;
	}
}

/*
 *	o_process_functions_in_node -
 *	  apply checker() to each function OID contained in given expression node
 *
 * Returns true if the checker() function does; for nodes representing more
 * than one function call, returns true if the checker() function does so
 * for any of those functions.  Returns false if node does not invoke any
 * SQL-visible function.  Caller must not pass node == NULL.
 *
 * This function examines only the given node; it does not recurse into any
 * sub-expressions.  Callers typically prefer to keep control of the recursion
 * for themselves, in case additional checks should be made, or because they
 * have special rules about which parts of the tree need to be visited.
 *
 * Note: we ignore MinMaxExpr, SQLValueFunction, XmlExpr, CoerceToDomain,
 * and NextValueExpr nodes, because they do not contain SQL function OIDs.
 * However, they can invoke SQL-visible functions, so callers should take
 * thought about how to treat them.
 */
void
o_process_functions_in_node(Node *node,
							void (*func_walker)(Oid functionId,
												Oid inputcollid,
												List *args,
												void *context),
							void *context)
{
	Oid			functionId = InvalidOid;
	Oid			inputcollid;
	List	   *args;

	switch (nodeTag(node))
	{
		case T_Aggref:
			{
				Aggref	   *expr = (Aggref *) node;

				functionId = expr->aggfnoid;
				inputcollid = expr->inputcollid;
				args = expr->args;

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_WindowFunc:
			{
				WindowFunc *expr = (WindowFunc *) node;

				functionId = expr->winfnoid;
				inputcollid = expr->inputcollid;
				args = expr->args;

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_FuncExpr:
			{
				FuncExpr   *expr = (FuncExpr *) node;

				functionId = expr->funcid;
				inputcollid = expr->inputcollid;
				args = expr->args;

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_OpExpr:
		case T_DistinctExpr:	/* struct-equivalent to OpExpr */
		case T_NullIfExpr:		/* struct-equivalent to OpExpr */
			{
				OpExpr	   *expr = (OpExpr *) node;

				/* Set opfuncid if it wasn't set already */
				set_opfuncid(expr);

				functionId = expr->opfuncid;
				inputcollid = expr->inputcollid;
				args = expr->args;

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr *expr = (ScalarArrayOpExpr *) node;

				set_sa_opfuncid(expr);
				functionId = expr->opfuncid;
				inputcollid = expr->inputcollid;
				args = expr->args;

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_CoerceViaIO:
			{
				CoerceViaIO *expr = (CoerceViaIO *) node;
				Oid			iofunc;
				Oid			typioparam;
				bool		typisvarlena;

				/* check the result type's input function */
				getTypeInputInfo(expr->resulttype,
								 &iofunc, &typioparam);

				functionId = iofunc;
				inputcollid = InvalidOid;
				args = list_make1(expr->arg);

				func_walker(functionId, inputcollid, args, context);

				/* check the input type's output function */
				getTypeOutputInfo(exprType((Node *) expr->arg),
								  &iofunc, &typisvarlena);

				functionId = iofunc;
				inputcollid = InvalidOid;
				args = list_make1(expr->arg);

				func_walker(functionId, inputcollid, args, context);
			}
			break;
		case T_RowCompareExpr:
			{
				RowCompareExpr *rcexpr = (RowCompareExpr *) node;
				ListCell   *opid;
				ListCell   *collid;
				ListCell   *larg;
				ListCell   *rarg;

				forfour(opid, rcexpr->opnos,
						collid, rcexpr->inputcollids,
						larg, rcexpr->largs,
						rarg, rcexpr->rargs)
				{
					functionId = get_opcode(lfirst_oid(opid));
					inputcollid = lfirst_oid(collid);
					args = list_make2(lfirst(larg),
									  lfirst(rarg));

					func_walker(functionId, inputcollid, args, context);
				}
			}
			break;
		default:
			break;
	}
}
