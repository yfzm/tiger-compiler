#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/
const int F_wordSize = 8;
static Temp_temp rax = NULL;
static Temp_temp rbx = NULL;
static Temp_temp rsp = NULL;
static Temp_temp rbp = NULL;

static Temp_temp rdi = NULL;
static Temp_temp rsi = NULL;
static Temp_temp rdx = NULL;
static Temp_temp rcx = NULL;
static Temp_temp r8 = NULL;
static Temp_temp r9 = NULL;
static Temp_temp r10 = NULL;
static Temp_temp r11 = NULL;
static Temp_temp r12 = NULL;
static Temp_temp r13 = NULL;
static Temp_temp r14 = NULL;
static Temp_temp r15 = NULL;

Temp_temp F_RBP() {
	if (rbp == NULL) rbp = Temp_newtemp();
	return rbp;
}

Temp_temp F_RSP() {
	if (rsp == NULL) rsp = Temp_newtemp();
	return rsp;
}

Temp_temp F_RAX() {
	if (rax == NULL) rax = Temp_newtemp();
	return rax;
}

Temp_temp F_RBX() {
	if (rbx == NULL) rbx = Temp_newtemp();
	return rbx;
}

Temp_temp F_RDI() {
	if (rdi == NULL) rdi = Temp_newtemp();
	return rdi;
}

Temp_temp F_RSI() {
	if (rsi == NULL) rsi = Temp_newtemp();
	return rsi;
}

Temp_temp F_RDX() {
	if (rdx == NULL) rdx = Temp_newtemp();
	return rdx;
}

Temp_temp F_RCX() {
	if (rcx == NULL) rcx = Temp_newtemp();
	return rcx;
}

Temp_temp F_R8() {
	if (r8 == NULL) r8 = Temp_newtemp();
	return r8;
}

Temp_temp F_R9() {
	if (r9 == NULL) r9 = Temp_newtemp();
	return r9;
}

Temp_temp F_R10() {
	if (r10 == NULL) r10 = Temp_newtemp();
	return r10;
}

Temp_temp F_R11() {
	if (r11 == NULL) r11 = Temp_newtemp();
	return r11;
}

Temp_temp F_R12() {
	if (r12 == NULL) r12 = Temp_newtemp();
	return r12;
}

Temp_temp F_R13() {
	if (r13 == NULL) r13 = Temp_newtemp();
	return r13;
}

Temp_temp F_R14() {
	if (r14 == NULL) r14 = Temp_newtemp();
	return r14;
}

Temp_temp F_R15() {
	if (r15 == NULL) r15 = Temp_newtemp();
	return r15;
}

Temp_temp F_FKE() {
	static Temp_temp fke;
	if (fke == NULL) fke = Temp_newtemp();
	return fke;
}
/*
            emit(AS_Move("movq `s0, `d0", L(F_RDI(), NULL), L(rdi_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_RSI(), NULL), L(rsi_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_RDX(), NULL), L(rdx_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_RCX(), NULL), L(rcx_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_RAX(), NULL), L(rax_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_R8(), NULL), L(r8_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_R9(), NULL), L(r9_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_R10(), NULL), L(r10_bk, NULL)));
            emit(AS_Move("movq `s0, `d0", L(F_R11(), NULL), L(r11_bk, NULL)));
*/

Temp_tempList F_calldefs() {
	return Temp_TempList(F_RAX(),
		Temp_TempList(F_RDI(),
		Temp_TempList(F_RSI(),
		Temp_TempList(F_RDX(),
		Temp_TempList(F_RCX(),
		Temp_TempList(F_R8(),
		Temp_TempList(F_R9(),
		Temp_TempList(F_R10(),
		Temp_TempList(F_R11(),
		NULL)))))))));
}

Temp_tempList F_hardRegs() {
	return Temp_TempList(F_RAX(),
		Temp_TempList(F_RBX(),
		Temp_TempList(F_RDI(),
		Temp_TempList(F_RSI(),
		Temp_TempList(F_RDX(),
		Temp_TempList(F_RCX(),
		Temp_TempList(F_R8(),
		Temp_TempList(F_R9(),
		Temp_TempList(F_R10(),
		Temp_TempList(F_R11(),
		Temp_TempList(F_R12(),
		Temp_TempList(F_R13(),
		Temp_TempList(F_R14(),
		Temp_TempList(F_R15(),
		Temp_TempList(F_RBP(),
		NULL)))))))))))))));
}

struct F_frame_ {
	Temp_label name;
	F_accessList accessList;
	int local_num;
	TAB_table tempAccessList;
};

//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

static F_access InFrame(int offset) {
	F_access access = checked_malloc(sizeof(*access));
	access->kind = inFrame;
	access->u.offset = offset;
	return access;
}

static F_access InReg(Temp_temp reg) {
	F_access access = checked_malloc(sizeof(*access));
	access->kind = inReg;
	access->u.reg = reg;
	return access;
}

F_accessList F_AccessList(F_access head, F_accessList tail) {
	F_accessList al = checked_malloc(sizeof(*al));
	al->head = head;
	al->tail = tail;
	return al;
}

F_accessList F_reverseAcessList(F_accessList al) {
	F_accessList ret = NULL;
	for (; al; al = al->tail) {
		ret = F_AccessList(al->head, ret);
	}
	return ret;
}

F_accessList bool2access(U_boolList formals) {
	int offset = 0;
	F_accessList ret = NULL;
	while (formals) {
		F_accessList al = checked_malloc(sizeof(*al));
		if (formals->head) {
			ret = F_AccessList(InFrame(offset), ret);
			offset += 8;
			
		} else {
			ret = F_AccessList(InReg(Temp_newtemp()), ret);
		}
		formals = formals->tail;
	}
	return F_reverseAcessList(ret);
}

F_frame F_newFrame(Temp_label name, U_boolList formals) {
	F_frame frame = checked_malloc(sizeof(*frame));
	frame->name = name;
	frame->accessList = bool2access(formals);
	
	int init_num = 0;
	for (U_boolList bl = formals; bl; bl = bl->tail) {
		if (bl->head) init_num++;
	}

	frame->local_num = init_num;
	frame->tempAccessList = TAB_empty();
	return frame;
}

Temp_label F_name(F_frame f) {
	return f->name;
}

F_accessList F_formals(F_frame f) {
	return f->accessList;
}

F_access F_allocLocal(F_frame f, bool escape) {
	if (escape) {
		int off = F_wordSize * (f->local_num);
		f->local_num++;
		return InFrame(off);
	} else {
		return InReg(Temp_newtemp());
	}
}

F_frag F_StringFrag(Temp_label label, string str) {
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_stringFrag;
	frag->u.stringg.label = label;

	int len = strlen(str);
	char *astr = checked_malloc(len + 5);
	memset(astr, 0, len + 5);
	*(int*)astr = len;
	strncpy(astr+4, str, len);

	frag->u.stringg.str = astr;
	return frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame) {
	F_frag frag = checked_malloc(sizeof(*frag));
	frag->kind = F_procFrag;
	frag->u.proc.body = body;
	frag->u.proc.frame = frame;
	return frag;
}
                                                      
F_fragList F_FragList(F_frag head, F_fragList tail) { 
	F_fragList fragList = checked_malloc(sizeof(*fragList));
	fragList->head = head;
	fragList->tail = tail;
	return fragList;
}                                                     

T_exp F_externalCall(string s, T_expList args) {
	return T_Call(T_Name(Temp_namedlabel(s)), args);
}

T_exp F_Exp(F_access acc, T_exp framePtr) {
	// printf("F_Exp type: %d, %d\n", acc->kind, acc->u.offset);
	switch (acc->kind) {
		case inFrame:
			return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));
		case inReg:
			return T_Temp(acc->u.reg);
	}
}

int F_spill(F_frame f) {
	return 0;
}

string Temp_tempName(Temp_temp t) {
	if (t == rax) return "rax";
	if (t == rbx) return "rbx";
	if (t == rsp) return "rsp";
	if (t == rbp) return "rbp";
	if (t == rdi) return "rdi";
	if (t == rsi) return "rsi";
	if (t == rdx) return "rdx";
	if (t == rcx) return "rcx";
	if (t == r8 ) return "r8 ";
	if (t == r9 ) return "r9 ";
	if (t == r10) return "r10";
	if (t == r11) return "r11";
	if (t == r12) return "r12";
	if (t == r13) return "r13";
	if (t == r14) return "r14";
	if (t == r15) return "r15";
	return "^-^";
}

// static Temp_temp rax = NULL;
// static Temp_temp rbx = NULL;
// static Temp_temp rsp = NULL;
// static Temp_temp rbp = NULL;

// static Temp_temp rdi = NULL;
// static Temp_temp rsi = NULL;
// static Temp_temp rdx = NULL;
// static Temp_temp rcx = NULL;
// static Temp_temp r8 = NULL;
// static Temp_temp r9 = NULL;
// static Temp_temp r10 = NULL;
// static Temp_temp r11 = NULL;
// static Temp_temp r12 = NULL;
// static Temp_temp r13 = NULL;
// static Temp_temp r14 = NULL;
// static Temp_temp r15 = NULL;

int F_size(F_frame f) {
	return f->local_num * F_wordSize;
}

void F_saveSpill(F_frame f, Temp_temp t, F_access ac) {
	TAB_enter(f->tempAccessList, t, ac);
	// f->tempAccessList = F_AccessList(ac, f->tempAccessList);
}


int F_loadSpill(F_frame f, Temp_temp t) {
	// F_access ac = f->tempAccessList->head;
	F_access ac = TAB_look(f->tempAccessList, t);
	assert(ac);
	assert(ac->kind == inFrame);
	// f->tempAccessList = f->tempAccessList->tail;
	return ac->u.offset;
}