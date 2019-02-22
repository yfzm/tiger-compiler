#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"

/*Lab5: Your implementation of lab5.*/

struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty checkType(S_table tenv, S_symbol sym, int pos) {
	Ty_ty ty = S_look(tenv, sym);
	if (!ty) {
		EM_error(pos, "undefined type %s", S_name(sym));
		return NULL;
	}
	return ty;
}

int typeEqual(Ty_ty a, Ty_ty b) {
	a = actual_ty(a);
	b = actual_ty(b);
	if (a->kind == Ty_nil || b->kind == Ty_nil) return 1;

	if (a->kind != b->kind) return 0;

	// if (a->kind == Ty_array) return typeEqual(a->u.array, b->u.array);
	if (a->kind == Ty_array || a->kind == Ty_record) return a == b;
	return 1;
}

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level, Temp_label label) {
	switch (v->kind) {
		case A_simpleVar: {
			E_enventry x = S_look(venv, v->u.simple);
			if (x && x->kind == E_varEntry)
				return expTy(Tr_simpleVar(x->u.var.access, level), actual_ty(x->u.var.ty));
			EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
			return expTy(Tr_noExp(), Ty_Int());
		}
		case A_fieldVar: {
			struct expty base = transVar(venv, tenv, get_fieldvar_var(v), level, label);
			Ty_ty base_ty = actual_ty(base.ty);
			if (base_ty->kind != Ty_record) {
				EM_error(v->pos, "not a record type");
				return expTy(Tr_noExp(), Ty_Nil());
			}
			S_symbol sym = get_fieldvar_sym(v);
			Ty_fieldList list = base.ty->u.record;
			int index = 0;
			while (list) {
				if (!strcmp(S_name(list->head->name), S_name(sym))) {
					return expTy(Tr_filedVar(base.exp, index), list->head->ty);
				}
				list = list->tail;
				index++;
			}
			EM_error(v->pos, "field %s doesn't exist", S_name(sym));
			return expTy(Tr_noExp(), Ty_Nil());
			break;
		}
		case A_subscriptVar: {
			struct expty base = transVar(venv, tenv, get_subvar_var(v), level, label);
			Ty_ty base_ty = actual_ty(base.ty);
			if (base_ty->kind != Ty_array) {
				EM_error(v->pos, "array type required");
				return expTy(Tr_noExp(), Ty_Nil());
			}
			struct expty index = transExp(venv, tenv, get_subvar_exp(v), level, label);
			if (actual_ty(index.ty)->kind != Ty_int) {
				EM_error(v->pos, "array index error!");
				return expTy(Tr_noExp(), Ty_Nil());
			}
			return expTy(Tr_subscriptVar(base.exp, index.exp), base_ty->u.array);
		}
	}
	return expTy(Tr_noExp(), Ty_Void());
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label label) {
	switch (a->kind) {
		case A_varExp: {
			return transVar(venv, tenv, a->u.var, level, label);
		}
		case A_nilExp: {
			return expTy(Tr_nilExp(), Ty_Nil());
		}
		case A_intExp: {
			return expTy(Tr_intExp(a->u.intt), Ty_Int());
		}
		case A_stringExp: {
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());
		}
		case A_callExp: {
			E_enventry func = S_look(venv, a->u.call.func);
			if (!func) {
				EM_error(a->pos, "undefined function %s", S_name(get_callexp_func(a)));
				return expTy(Tr_noExp(), Ty_Void());
			}
			Ty_tyList formals = func->u.fun.formals;
			A_expList args = get_callexp_args(a);
			Tr_expList argList = NULL;
			while (args && formals) {
				struct expty argty = transExp(venv, tenv, args->head, level, label);
				assert(argty.ty);
				if (!typeEqual(argty.ty, formals->head)) {
					EM_error(get_callexp_args(a)->head->pos, "para type mismatch");
					return expTy(Tr_noExp(), Ty_Void());
				}
				argList = Tr_ExpList(argty.exp, argList);
				args = args->tail;
				formals = formals->tail;
			}

			if (args) 
				EM_error(a->pos, "too many params in function %s", S_name(get_callexp_func(a)));

			Ty_ty result = func->u.fun.result;
			Tr_exp trexp = Tr_callExp(level, func->u.fun.level, Temp_namedlabel(S_name(a->u.call.func)), argList);
			if (!result || result->kind == Ty_void) return expTy(trexp, Ty_Void());
			return expTy(trexp, result);
		}
		case A_opExp: {
			A_oper oper = a->u.op.oper;
			struct expty left = transExp(venv, tenv, a->u.op.left, level, label);
			struct expty right = transExp(venv, tenv, a->u.op.right, level, label);
			if (oper == A_eqOp && left.ty->kind == Ty_string && right.ty->kind == Ty_string) {
				return expTy(Tr_strEqual(left.exp, right.exp), Ty_Int());
			}
			switch (oper) {
				case A_plusOp:
				case A_minusOp:
				case A_timesOp:
				case A_divideOp: {
					if (left.ty->kind != Ty_int)
						EM_error(a->u.op.left->pos, "integer required");
					if (right.ty->kind != Ty_int)
						EM_error(a->u.op.right->pos, "integer required");
					// TODO: Error handling
					return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
				}
				case A_ltOp: case A_leOp: case A_eqOp:
				case A_gtOp: case A_geOp: case A_neqOp: {
					if (!typeEqual(left.ty, right.ty)) {
						EM_error(a->u.op.right->pos, "same type required");
					}
					return expTy(Tr_opExp(oper, left.exp, right.exp), Ty_Int());
				}
			}
			return expTy(Tr_noExp(), Ty_Int());
		}
		case A_recordExp: {
			Ty_ty ty = checkType(tenv, get_recordexp_typ(a), a->pos);
			if (!ty) return expTy(Tr_noExp(), Ty_Record(NULL));
			
			ty = actual_ty(ty);
			if (ty->kind != Ty_record) {
				EM_error(a->pos, "type error in record\n");
				return expTy(Tr_noExp(), Ty_Record(NULL));
			}

			Tr_expList expList = NULL;
			Ty_fieldList expects = ty->u.record;
			A_efieldList actuals = get_recordexp_fields(a);
			while (actuals && expects) {
				if (strcmp(S_name(actuals->head->name), S_name(expects->head->name))) {
					EM_error(a->pos, "type wrong in recordExp");
					return expTy(Tr_noExp(), ty);
				}
				struct expty val = transExp(venv, tenv, actuals->head->exp, level, label);
				if (!typeEqual(val.ty, expects->head->ty)) {
					EM_error(a->pos, "recordExp!!!");
					return expTy(Tr_noExp(), ty);
				}
				expList = Tr_ExpList(val.exp, expList);
				actuals = actuals->tail;
				expects = expects->tail;
			}
			if (actuals || expects) {
				EM_error(a->pos, "recordExp: num??");
			}
			expList = Tr_reverseList(expList);  // Get the right order!!
			return expTy(Tr_recordExp(expList), ty);
		}
		case A_seqExp: {
			A_expList seq = get_seqexp_seq(a);
			Tr_exp exps = Tr_nilExp();
			if (!seq) return expTy(exps, Ty_Void());
			struct expty et;
			while (seq) {
				et = transExp(venv, tenv, seq->head, level, label);
				exps = Tr_seqExp(exps, et.exp);
				seq = seq->tail;
			}
			return expTy(exps, et.ty);
		}
		case A_assignExp: {
			if (a->u.assign.var->kind == A_simpleVar) {
				E_enventry entry = S_look(venv, a->u.assign.var->u.simple);
				if (entry && entry->readonly) {
					EM_error(a->u.assign.var->pos, "loop variable can't be assigned");
					return expTy(Tr_noExp(), Ty_Void());
				}
			}

			struct expty var = transVar(venv, tenv, a->u.assign.var, level, label);
			struct expty val = transExp(venv, tenv, a->u.assign.exp, level, label);
			if (!typeEqual(var.ty, val.ty)) {
				EM_error(a->u.assign.exp->pos, "unmatched assign exp");
				return expTy(Tr_noExp(), Ty_Void());
			}
			return expTy(Tr_assignExp(var.exp, val.exp), Ty_Void());
		}
		case A_ifExp: {
			struct expty condition = transExp(venv, tenv, a->u.iff.test, level, label);
			if (condition.ty->kind != Ty_int) {
				EM_error(a->u.iff.test->pos, "iffffffffffffffcondition");
				return expTy(Tr_noExp(), Ty_Int());
			}

			struct expty then = transExp(venv, tenv, a->u.iff.then, level, label);
			
			if (a->u.iff.elsee) {
				struct expty elsee = transExp(venv, tenv, a->u.iff.elsee, level, label);
				if (!typeEqual(then.ty, elsee.ty)) {
					EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
					return expTy(Tr_noExp(), Ty_Nil());
				}
				return expTy(Tr_ifExp(condition.exp, then.exp, elsee.exp), then.ty);

			}
			if (then.ty->kind != Ty_nil && then.ty->kind != Ty_void) {
				EM_error(get_ifexp_then(a)->pos, "if-then exp's body must produce no value");
				return expTy(Tr_noExp(), Ty_Void());
			}
			return expTy(Tr_ifExp(condition.exp, then.exp, NULL), Ty_Void());

		}
		case A_whileExp: {
			Temp_label done = Temp_newlabel();
			struct expty test = transExp(venv, tenv, a->u.whilee.test, level, label);
			if (test.ty->kind != Ty_int)
				EM_error(a->u.whilee.test->pos, "whileeeeeeeecondition");
			struct expty body = transExp(venv, tenv, a->u.whilee.body, level, done);
			if (body.ty->kind != Ty_void)
				EM_error(a->u.whilee.body->pos, "while body must produce no value");
			return expTy(Tr_whileExp(test.exp, body.exp, done), Ty_Void());
		}
		case A_forExp: {
			Temp_label done = Temp_newlabel();
			struct expty lo = transExp(venv, tenv, a->u.forr.lo, level, label);
			struct expty hi = transExp(venv, tenv, a->u.forr.hi, level, label);
			if (lo.ty->kind != Ty_int)
				EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
			if (hi.ty->kind != Ty_int)
				EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
			S_beginScope(venv);
			S_beginScope(tenv);
			Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
			S_enter(venv, a->u.forr.var, E_ROVarEntry(access, Ty_Name(a->u.forr.var, hi.ty)));
			struct expty body = transExp(venv, tenv, a->u.forr.body, level, done);
			if (body.ty->kind != Ty_void)
				EM_error(a->u.whilee.body->pos, "for body must produce no value");
			S_endScope(tenv);
			S_endScope(venv);
			return expTy(Tr_forExp(access, lo.exp, hi.exp, body.exp, done), Ty_Void());
		}
		case A_breakExp: {
			if (label == NULL) {
				EM_error(a->pos, "loop label is not inside a loop");
				return expTy(Tr_noExp(), Ty_Void());
			}
			return expTy(Tr_jump(label), Ty_Void());
		}
		case A_letExp: {
			struct expty exp;
			Tr_exp e = Tr_nilExp();
			A_decList d;
			S_beginScope(venv);
			S_beginScope(tenv);
			for (d = get_letexp_decs(a); d; d = d->tail)
				e = Tr_seqExp(e, transDec(venv, tenv, d->head, level, label));
			exp = transExp(venv, tenv, get_letexp_body(a), level, label);
			exp.exp = Tr_seqExp(e, exp.exp);
			S_endScope(tenv);
			S_endScope(venv);
			return exp;
		}
		case A_arrayExp: {
			Ty_ty ty = checkType(tenv, get_arrayexp_typ(a), a->pos);
			if (ty) {
				ty = actual_ty(ty);
				if (ty->kind != Ty_array) {
					EM_error(a->pos, "type error in array\n");
					ty = Ty_Array(Ty_Int());
				}
			} else
				ty = Ty_Array(Ty_Int());
			struct expty size = transExp(venv, tenv, get_arrayexp_size(a), level, label);
			struct expty init = transExp(venv, tenv, get_arrayexp_init(a), level, label);

			if (size.ty->kind != Ty_int) {
				EM_error(a->pos, "array: not integer!");
				return expTy(Tr_noExp(), Ty_Nil());
			}

			if (!typeEqual(init.ty, ty->u.array)) {
				EM_error(a->pos, "type mismatch");
				return expTy(Tr_noExp(), Ty_Nil());
			}

			return expTy(Tr_arrayExp(size.exp, init.exp), ty);
		}

	}
	return expTy(Tr_noExp(), Ty_Void());
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList fl) {
	if (!fl) return NULL;
	Ty_ty ty = checkType(tenv, fl->head->typ, fl->head->pos);
	if (!ty) ty = Ty_Int();
	return Ty_TyList(ty, makeFormalTyList(tenv, fl->tail));
}

U_boolList makeFormalEscapeList(A_fieldList fl) {
	if (!fl) return NULL;
	return U_BoolList(fl->head->escape, makeFormalEscapeList(fl->tail));
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label label) {
	switch (d->kind) {
		case A_functionDec: {
			A_fundecList list = get_funcdec_list(d);

			// check same name
			while (list) {
				S_symbol base = list->head->name;
				A_fundecList help = list->tail;
				while (help) {
					if (!strcmp(S_name(base), S_name(help->head->name))) {
						EM_error(d->pos, "two functions have the same name");
						return Tr_noExp();
					}
					help = help->tail;
				}
				list = list->tail;
			}

			list = get_funcdec_list(d);
			while (list) {
				A_fundec f = list->head;
				Ty_ty resultTy;
				if (f->result) {
					resultTy = checkType(tenv, f->result, f->pos);
				} else {
					resultTy = Ty_Void();
				}
				Ty_tyList fromalTys = makeFormalTyList(tenv, f->params);
				U_boolList formalEscapes = makeFormalEscapeList(f->params);
				Temp_label fun_label = Temp_namedlabel(S_name(f->name));
				Tr_level fun_level = Tr_newLevel(level, fun_label, formalEscapes);
				S_enter(venv, f->name, E_FunEntry(fun_level, fun_label, fromalTys, resultTy));
				list = list->tail;
			}
			
			list = get_funcdec_list(d);
			while (list) {
				A_fundec f = list->head;
				E_enventry func = S_look(venv, f->name);

				Ty_tyList fromalTys = func->u.fun.formals;
				S_beginScope(venv);
				A_fieldList l;
				Ty_tyList t;
				Tr_accessList formalAccessList = Tr_formals(func->u.fun.level);
				Tr_accessList fa = Tr_getNextAccess(formalAccessList);  // just for loop and skip static link
				for (l = f->params, t = fromalTys; l; l = l->tail, t = t->tail, fa = Tr_getNextAccess(fa)) {
					S_enter(venv, l->head->name, E_VarEntry(Tr_getAccess(fa), t->head));
				}
				struct expty fun_ret = transExp(venv, tenv, f->body, func->u.fun.level, label);
				if (f->result == NULL) {
					if (fun_ret.ty->kind != Ty_void) {
						EM_error(f->pos, "procedure returns value");
						func->u.fun.result = fun_ret.ty;
					}
				} else {
					if (!typeEqual(fun_ret.ty, func->u.fun.result)) {
						EM_error(f->pos, "lalalain_funcdeclist");
						func->u.fun.result = fun_ret.ty;
					}
				}
				Tr_procEntryExit(func->u.fun.level, fun_ret.exp, formalAccessList);
				S_endScope(venv);
				list = list->tail;
			}

			return Tr_noExp();
		}
		case A_varDec: {
			struct expty e = transExp(venv, tenv, get_vardec_init(d), level, label);
			S_symbol typ = get_vardec_typ(d);
			if (typ != NULL) {
				Ty_ty ty = checkType(tenv, typ, d->pos);
				if (!ty) return Tr_noExp();
				if (!typeEqual(ty, e.ty)) {
					EM_error(d->pos, "type mismatch");
				}
			} else {
				if (e.ty->kind == Ty_nil) {
					EM_error(d->pos, "init should not be nil without type specified");
					// return;
				}
			}
			Tr_access access = Tr_allocLocal(level, d->u.var.escape);
			S_enter(venv, d->u.var.var, E_VarEntry(access, e.ty));
			return Tr_assignExp(Tr_simpleVar(access, level), e.exp);
		}
		case A_typeDec: {
			A_nametyList list = get_typedec_list(d);

			// check same types
			while (list) {
				S_symbol base = list->head->name;
				A_nametyList help = list->tail;
				while (help) {
					if (!strcmp(S_name(base), S_name(help->head->name))) {
						EM_error(d->pos, "two types have the same name");
						return Tr_noExp();
					}
					help = help->tail;
				}
				list = list->tail;
			}

			// add all types
			list = get_typedec_list(d);
			while (list) {
				S_enter(tenv, list->head->name, Ty_Name(list->head->name, NULL));
				list = list->tail;
			}

			// fill actual types and check cycle
			list = get_typedec_list(d);
			while (list) {
				Ty_ty ori = S_look(tenv, list->head->name);
				Ty_ty ty = transTy(tenv, list->head->ty);
				ori->u.name.ty = ty;

				while (ty && ty->kind == Ty_name) {
					if (ty == ori) {
						EM_error(d->pos, "illegal type cycle");
						S_enter(tenv, list->head->name, Ty_Int());
						break;
					}
					ty = ty->u.name.ty;
				}
				list = list->tail;
			}

			break;
		}
	}
}

Ty_fieldList transFieldList(S_table tenv, A_fieldList record) {
	if (!record) return NULL;
	Ty_ty ty = checkType(tenv, record->head->typ, record->head->pos);
	if (!ty) ty = Ty_Int();
	return Ty_FieldList(Ty_Field(record->head->name, ty), transFieldList(tenv, record->tail));
}

Ty_ty transTy (S_table tenv, A_ty a) {
	switch (a->kind) {
		case A_nameTy: {
			Ty_ty ty = checkType(tenv, get_ty_name(a), a->pos);
			if (!ty) ty = Ty_Int();
			return Ty_Name(get_ty_name(a), ty);
		}
		case A_recordTy: {
			return Ty_Record(transFieldList(tenv, get_ty_record(a)));
		}
		case A_arrayTy: {
			Ty_ty ty = checkType(tenv, get_ty_array(a), a->pos);
			if (!ty) ty = Ty_Int();
			return Ty_Array(actual_ty(ty));
		}
	}
}


F_fragList SEM_transProg(A_exp exp){
	struct expty e = transExp(E_base_venv(), E_base_tenv(), exp, Tr_outermost(), NULL);
	Tr_procEntryExit(Tr_outermost(), e.exp, NULL);
	return Tr_getResult();
}

