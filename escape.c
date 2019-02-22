#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"
#include "helper.h"

typedef struct Esc_escentry_ *Esc_escentry;

struct Esc_escentry_ {
    int depth;
    bool *esc;
};

Esc_escentry EscapeEnrty(int d, bool *e) {
	Esc_escentry entry = checked_malloc(sizeof(*entry));
	entry->depth = d;
	entry->esc = e;
	return entry;
}
static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);

static void traverseExp(S_table env, int depth, A_exp e) {
	switch (e->kind) {
		case A_varExp: {
			traverseVar(env, depth, e->u.var);
			break;
		}
		case A_nilExp:
		case A_intExp:
		case A_stringExp:
			break;
		case A_callExp: {
			A_expList args = get_callexp_args(e);
			while (args) {
				traverseExp(env, depth, args->head);
				args = args->tail;
			}
			break;
		}
		case A_opExp: {
			traverseExp(env, depth, e->u.op.left);
			traverseExp(env, depth, e->u.op.right);
			break;
		}
		case A_recordExp: {
			A_efieldList actuals = get_recordexp_fields(e);
			while (actuals) {
				traverseExp(env, depth, actuals->head->exp);
				actuals = actuals->tail;
			}
			break;
		}
		case A_seqExp: {
			A_expList seq = get_seqexp_seq(e);
			while (seq) {
				traverseExp(env, depth, seq->head);				
				seq = seq->tail;
			}
			break;
		}
		case A_assignExp: {
			traverseExp(env, depth, e->u.assign.exp);
			traverseVar(env, depth, e->u.assign.var);
			break;
		}
		case A_ifExp: {
			traverseExp(env, depth, e->u.iff.test);
			traverseExp(env, depth, e->u.iff.then);
			if (e->u.iff.elsee) {
				traverseExp(env, depth, e->u.iff.elsee);
			}
			break;
		}
		case A_whileExp: {
			traverseExp(env, depth, e->u.whilee.test);
			traverseExp(env, depth, e->u.whilee.body);
			break;
		}
		case A_forExp: {
			traverseExp(env, depth, e->u.forr.lo);
			traverseExp(env, depth, e->u.forr.hi);
			S_beginScope(env);
			e->u.forr.escape = FALSE;
			S_enter(env, e->u.forr.var, EscapeEnrty(depth, &(e->u.forr.escape)));
			traverseExp(env, depth, e->u.forr.body);
			S_endScope(env);
			break;
		}
		case A_breakExp: {
			break;
		}
		case A_letExp: {
			A_decList d;
			S_beginScope(env);
			for (d = get_letexp_decs(e); d; d = d->tail) {
				traverseDec(env, depth, d->head);
			}
			traverseExp(env, depth, e->u.let.body);
			S_endScope(env);
			break;
		}
		case A_arrayExp: {
			traverseExp(env, depth, e->u.array.size);
			traverseExp(env, depth, e->u.array.init);			
			break;
		}

	}

}

static void traverseDec(S_table env, int depth, A_dec d) {
	switch (d->kind) {
		case A_functionDec: {
			A_fundecList list = get_funcdec_list(d);
			while (list) {
				A_fundec f = list->head;
				S_beginScope(env);
				A_fieldList l;
				for (l = f->params; l; l = l->tail) {
					l->head->escape = FALSE;
					S_enter(env, l->head->name, EscapeEnrty(depth+1, &(l->head->escape)));
				}
				traverseExp(env, depth+1, f->body);
				S_endScope(env);
				list = list->tail;
			}
			break;
		}
		case A_varDec: {
			traverseExp(env, depth, d->u.var.init);
			d->u.var.escape = FALSE;
			S_enter(env, d->u.var.var, EscapeEnrty(depth, &(d->u.var.escape)));
			break;
		}
		case A_typeDec: {
			break;
		}
	}
}

static void traverseVar(S_table env, int depth, A_var v) {
	switch (v->kind) {
		case A_simpleVar: {
			Esc_escentry entry = S_look(env, v->u.simple);
			if (entry->depth < depth) {
				*(entry->esc) = TRUE;
			}
			break;
		}
		case A_fieldVar: {
			traverseVar(env, depth, v->u.field.var);
			break;
		}
		case A_subscriptVar: {
			traverseExp(env, depth, v->u.subscript.exp);
			traverseVar(env, depth, v->u.subscript.var);
			break;
		}
	}

}


void Esc_findEscape(A_exp exp) {
	traverseExp(S_empty(), 0, exp);
}
