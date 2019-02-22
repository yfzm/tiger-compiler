#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

struct Tr_access_ {
	Tr_level level;
	F_access access;
};


struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
	// Tr_accessList formals;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

struct Tr_expList_ {
	Tr_exp head;
	Tr_expList tail;
};

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail) {
	Tr_expList el = checked_malloc(sizeof(*el));
	el->head = head;
	el->tail = tail;
	return el;
}

Tr_access Tr_getAccess(Tr_accessList al) {
	return al->head;
}

Tr_accessList Tr_getNextAccess(Tr_accessList al) {
	return al->tail;
}

static patchList PatchList(Temp_label *head, patchList tail) {
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label) {
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second) {
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

static Tr_exp Tr_Ex(T_exp ex) {
	Tr_exp exp = checked_malloc(sizeof(struct Tr_exp_));
	exp->kind = Tr_ex;
	exp->u.ex = ex;
	return exp;
}

static Tr_exp Tr_Nx(T_stm nx) {
	// printf("Enter Tr_Nx\n");
	Tr_exp exp = checked_malloc(sizeof(struct Tr_exp_));
	exp->kind = Tr_nx;
	exp->u.nx = nx;
	return exp;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm) {
	Tr_exp exp = checked_malloc(sizeof(struct Tr_exp_));
	exp->kind = Tr_cx;
	exp->u.cx.trues = trues;
	exp->u.cx.falses = falses;
	exp->u.cx.stm = stm;
	return exp;
}

static T_exp unEx(Tr_exp e) {
	switch (e->kind) {
		case Tr_ex:
			return e->u.ex;
		case Tr_cx: {
			Temp_temp r = Temp_newtemp();
			Temp_label t = Temp_newlabel(), f = Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					T_Eseq(e->u.cx.stm,
					 T_Eseq(T_Label(f),
					  T_Eseq(T_Move(T_Temp(r), T_Const(0)),
					   T_Eseq(T_Label(t), T_Temp(r))))));
		}
		case Tr_nx:
			return T_Eseq(e->u.nx, T_Const(0));
	}
}

static T_stm unNx(Tr_exp e) {
	switch (e->kind) {
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx: {
			Temp_label l = Temp_newlabel();
			doPatch(e->u.cx.trues, l);
			doPatch(e->u.cx.falses, l);
			return T_Seq(e->u.cx.stm, T_Label(l));
		}
	}
}

static struct Cx unCx(Tr_exp e) {
	switch (e->kind) {
		case Tr_ex: {
			T_stm stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
			patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
			patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
			struct Cx cx;
			cx.trues = trues;
			cx.falses = falses;
			cx.stm = stm;
			return cx;
		}
		case Tr_nx: 
			assert(0);
		case Tr_cx: {
			return e->u.cx;
		}
	}
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail) {
	Tr_accessList al = checked_malloc(sizeof(*al));
	al->head = head;
	al->tail = tail;
	return al;
}

Tr_accessList Tr_reverseAccessList(Tr_accessList al) {
	Tr_accessList ret = NULL;
	for (; al; al = al->tail) {
		ret = Tr_AccessList(al->head, ret);
	}
	return ret;
}

static Tr_accessList makeAccessList(F_accessList formals, Tr_level level) {
	Tr_accessList al = NULL;
	while (formals) {
		Tr_access a = checked_malloc(sizeof(*a));
		a->access = formals->head;
		a->level = level;
		al = Tr_AccessList(a, al);
		formals = formals->tail;
	}
	return Tr_reverseAccessList(al);
}

static Tr_level outermost = NULL;
Tr_level Tr_outermost(void) {
	if (!outermost) {
		outermost = checked_malloc(sizeof(*outermost));
		outermost->parent = NULL;
		outermost->frame = F_newFrame(Temp_namedlabel("tigermain"), NULL);
	}
	return outermost;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals) {
	Tr_level level = checked_malloc(sizeof(*level));
	level->frame = F_newFrame(name, U_BoolList(1, formals));
	level->parent = parent;
	// level->formals = bool2traccess(formals);
	return level;
}

Tr_accessList Tr_formals(Tr_level level) {
	return makeAccessList(F_formals(level->frame), level);
}

Tr_access Tr_allocLocal(Tr_level level, bool escape) {
	Tr_access access = checked_malloc(sizeof(*access));
	access->access = F_allocLocal(level->frame, escape);
	access->level = level;
	return access;
}

static F_fragList fragList;
void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals) {
	// fragList = F_FragList(F_ProcFrag(unNx(body), level->frame), fragList);
	// View Change
	T_stm viewChange = T_Exp(T_Const(0));
	int count = 0;
	for (; formals; formals = formals->tail, count++) {
		T_exp src = NULL;
		switch (count) {
			case 0: src = T_Temp(F_RDI()); break;
			case 1: src = T_Temp(F_RSI()); break;
			case 2: src = T_Temp(F_RDX()); break;
			case 3: src = T_Temp(F_RCX()); break;
			case 4: src = T_Temp(F_R8()); break;
			case 5: src = T_Temp(F_R9()); break;
			default: src = T_Mem(T_Binop(T_plus, T_Temp(F_FKE()), T_Const((count-5)*8))); break;
		}
		T_exp dst = F_Exp(formals->head->access, T_Temp(F_RSP()));
		viewChange = T_Seq(viewChange, T_Move(dst, src));
	}

	T_stm total = T_Seq(viewChange, T_Move(T_Temp(F_RAX()), unEx(body)));

	fragList = F_FragList(F_ProcFrag(total, level->frame), fragList);
}

F_fragList Tr_getResult(void) {
	return fragList;
}


static T_expList exp_tr2t(Tr_expList tr) {
	T_expList t = NULL;
	while (tr) {
		t = T_ExpList(unEx(tr->head), t);
		tr = tr->tail;
	}
	return t;
}


Tr_exp Tr_noExp() {
	return NULL;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level) {
	T_exp static_link = T_Temp(F_RSP());
	for (; access->level != level; level = level->parent) {
		static_link = T_Mem(static_link);
	}
	T_exp exp = F_Exp(access->access, static_link);
	return Tr_Ex(exp);
}

Tr_exp Tr_filedVar(Tr_exp base, int index) {
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Const(index * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index) {
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Binop(T_mul, unEx(index), T_Const(F_wordSize)))));
}

Tr_exp Tr_nilExp() {
	return Tr_Ex(T_Const(0));
}

Tr_exp Tr_intExp(int n) {
	return Tr_Ex(T_Const(n));
}

Tr_exp Tr_stringExp(string str) {
	Temp_label label = Temp_newlabel();
	fragList = F_FragList(F_StringFrag(label, str), fragList);
	return Tr_Ex(T_Name(label));
}

// ATTENTION: args is in reserve order
Tr_exp Tr_callExp(Tr_level caller, Tr_level callee, Temp_label func, Tr_expList args) {
	T_expList expList = exp_tr2t(args);  // now expList is in regular order

	if (callee == outermost) {
		return Tr_Ex(F_externalCall(Temp_labelstring(func), expList));
	}

	// T_exp static_link = T_Temp(F_RBP());
	T_exp static_link = T_Temp(F_RSP());
	for (; caller != callee->parent; caller = caller->parent) {
		// static_link = T_Mem(T_Binop(T_plus, static_link, T_Const(0)));
		static_link = T_Mem(static_link);
	}
	expList = T_ExpList(static_link, expList);
	return Tr_Ex(T_Call(T_Name(func), expList));
}

Tr_exp Tr_opExp(A_oper op, Tr_exp left, Tr_exp right) {
	switch (op) {
		case A_plusOp:
			return Tr_Ex(T_Binop(T_plus, unEx(left), unEx(right)));
		case A_minusOp:
			return Tr_Ex(T_Binop(T_minus, unEx(left), unEx(right)));
		case A_timesOp:
			return Tr_Ex(T_Binop(T_mul, unEx(left), unEx(right)));
		case A_divideOp:
			return Tr_Ex(T_Binop(T_div, unEx(left), unEx(right)));
	}
	// noRel part
	T_stm stm;
	switch (op) {
		case A_eqOp:
			stm = T_Cjump(T_eq, unEx(left), unEx(right), NULL, NULL);
			break;
		case A_neqOp:
			stm = T_Cjump(T_ne, unEx(left), unEx(right), NULL, NULL);
			break;
		case A_ltOp:
			stm = T_Cjump(T_lt, unEx(left), unEx(right), NULL, NULL);
			break;
		case A_leOp:
			stm = T_Cjump(T_le, unEx(left), unEx(right), NULL, NULL);
			break;
		case A_geOp:
			stm = T_Cjump(T_ge, unEx(left), unEx(right), NULL, NULL);
			break;
		case A_gtOp:
			stm = T_Cjump(T_gt, unEx(left), unEx(right), NULL, NULL);
			break;
	}
	patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
	patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
	return Tr_Cx(trues,falses, stm);
}

Tr_exp Tr_strEqual(Tr_exp left, Tr_exp right) {
	// return 1 if equal
	T_exp call_strEqual = F_externalCall("stringEqual", T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
	T_stm stm = T_Cjump(T_eq, call_strEqual, T_Const(1), NULL, NULL);
	patchList trues = PatchList(&stm->u.CJUMP.true, NULL);
	patchList falses = PatchList(&stm->u.CJUMP.false, NULL);
	return Tr_Cx(trues, falses, stm);
}

Tr_exp Tr_recordExp(Tr_expList el) {
	int cnt = 0;
	Temp_temp base_ptr = Temp_newtemp();
	T_stm init = NULL;
	while (el) {
		T_stm stm = T_Move(T_Mem(T_Binop(T_plus, T_Temp(base_ptr),
			T_Binop(T_mul, T_Const(cnt), T_Const(F_wordSize)))), 
			unEx(el->head));
		init = (init == NULL) ? stm : T_Seq(stm, init);
		cnt++;
		el = el->tail;
	}
	assert(init != NULL);
	T_exp call_malloc = F_externalCall("malloc", T_ExpList(
		T_Binop(T_mul, T_Const(cnt), T_Const(F_wordSize)), NULL));
	return Tr_Ex(T_Eseq(T_Move(T_Temp(base_ptr), call_malloc),
		T_Eseq(init, T_Temp(base_ptr))));
}

Tr_exp Tr_seqExp(Tr_exp first, Tr_exp second) {
	if (second == NULL) {
		return first;
	}
	return Tr_Ex(T_Eseq(unNx(first), unEx(second)));
}

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp val) {
	return Tr_Nx(T_Move(unEx(var), unEx(val)));
}

Tr_exp Tr_ifExp(Tr_exp condition, Tr_exp then, Tr_exp elsee) {
	Temp_label t = Temp_newlabel();
	Temp_label f = Temp_newlabel();
	Temp_label done = Temp_newlabel();
	struct Cx cx = unCx(condition);
	doPatch(cx.trues, t);
	doPatch(cx.falses, f);

	if (elsee) {
		Temp_temp ret = Temp_newtemp();
		return Tr_Ex(T_Eseq(cx.stm, 
			T_Eseq(T_Label(t),
			 T_Eseq(T_Move(T_Temp(ret), unEx(then)),
			  T_Eseq(T_Jump(T_Name(done), Temp_LabelList(done, NULL)),
			   T_Eseq(T_Label(f),
			   	T_Eseq(T_Move(T_Temp(ret), unEx(elsee)),
				 T_Eseq(T_Label(done),
				  T_Temp(ret)))))))));
	} else {
		return Tr_Nx(T_Seq(cx.stm,
			 T_Seq(T_Label(t),
			  T_Seq(unNx(then),
			   T_Label(f)))));
	}
}

Tr_exp Tr_whileExp(Tr_exp condition, Tr_exp body, Temp_label done_label) {
	Temp_label cond_label = Temp_newlabel();
	Temp_label body_label = Temp_newlabel();
	// Temp_label done_label = Temp_newlabel();

	struct Cx cx = unCx(condition);
	doPatch(cx.trues, body_label);
	doPatch(cx.falses, done_label);

	return Tr_Nx(T_Seq(T_Label(cond_label),
		T_Seq(cx.stm,
		 T_Seq(T_Label(body_label),
		  T_Seq(unNx(body),
		   T_Seq(T_Jump(T_Name(cond_label), Temp_LabelList(cond_label, NULL)),
		    T_Label(done_label)))))));
}

Tr_exp Tr_forExp(Tr_access var_access, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done_label) {
	T_exp var = F_Exp(var_access->access, T_Temp(F_RSP()));
	T_exp limit = T_Temp(Temp_newtemp());

	// TODO: overflow!!
	Temp_label cond_label = Temp_newlabel();
	Temp_label body_label = Temp_newlabel();
	// Temp_label done_label = Temp_newlabel();

	// T_stm init = T_Seq(T_Move(var, unEx(lo)),
	// 	T_Seq(T_Move(limit, unEx(hi)), T_Label(cond_label)));

	// // T_stm for_cond = T_Seq(T_Label(cond_label),
	// // 	T_Cjump(T_le, var, limit, body_label, done_label));
	// T_stm for_cond = T_Cjump(T_le, var, limit, body_label, done_label);
	// T_stm for_body = T_Seq(T_Label(body_label), unNx(body));
	// T_stm for_incr = T_Seq(T_Move(var, T_Binop(T_plus, var, T_Const(1))),
	// 		  T_Seq(T_Jump(T_Name(cond_label), Temp_LabelList(cond_label, NULL)),
	// 		   T_Label(done_label)));

	// return Tr_Nx(T_Seq(init, T_Seq(for_cond, T_Seq(for_body, for_incr))));
	return Tr_Nx(T_Seq(T_Move(var, unEx(lo)),
		T_Seq(T_Move(limit, unEx(hi)),
		 T_Seq(T_Label(cond_label),
		  T_Seq(T_Cjump(T_le, var, limit, body_label, done_label),
		   T_Seq(T_Label(body_label),
		    T_Seq(unNx(body),
			 T_Seq(T_Move(var, T_Binop(T_plus, var, T_Const(1))),
			  T_Seq(T_Jump(T_Name(cond_label), Temp_LabelList(cond_label, NULL)),
			   T_Label(done_label))))))))));
}

Tr_exp Tr_jump(Temp_label label) {
	return Tr_Nx(T_Jump(T_Name(label), Temp_LabelList(label, NULL)));
}

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init) {
	// printf("Tr_arrayExp: size:%d, init:%d\n", );
	// T_exp call_malloc = F_externalCall("malloc", T_ExpList(
	// 	T_Binop(T_mul, unEx(size), T_Const(F_wordSize)), NULL));
	// int cnt = 0;
	// Temp_temp base_ptr = Temp_newtemp();
	// T_stm assign_stm;
	// while (size-->0) {
	// 	T_stm stm = T_Move(T_Binop(T_plus, T_Temp(base_ptr),
	// 		T_Binop(T_mul, T_Const(cnt), T_Const(F_wordSize))), 
	// 		unEx(init));
	// 	assign_stm = T_Seq(stm, assign_stm);
	// 	cnt++;
	// }

	// return Tr_Ex(T_Eseq(T_Move(T_Temp(base_ptr), call_malloc),
	// 	T_Eseq(assign_stm, T_Temp(base_ptr))));
	return Tr_Ex(F_externalCall(String("initArray"), 
		T_ExpList(unEx(size), T_ExpList(unEx(init), NULL))));
}

Tr_expList Tr_reverseList(Tr_expList el) {
	Tr_expList ret = NULL;
	for (; el; el = el->tail) {
		ret = Tr_ExpList(el->head, ret);
	}
	return ret;
}