
/*Lab5: This header file is not complete. Please finish it with more definition.*/

#ifndef FRAME_H
#define FRAME_H

#include "tree.h"

typedef struct F_frame_ *F_frame;

typedef struct F_access_ *F_access;
typedef struct F_accessList_ *F_accessList;

struct F_accessList_ {F_access head; F_accessList tail;};

F_frame F_newFrame(Temp_label name, U_boolList formals);
F_accessList F_AccessList(F_access head, F_accessList tail);

/* declaration for fragments */
typedef struct F_frag_ *F_frag;
struct F_frag_ {enum {F_stringFrag, F_procFrag} kind;
			union {
				struct {Temp_label label; string str;} stringg;
				struct {T_stm body; F_frame frame;} proc;
			} u;
};

F_frag F_StringFrag(Temp_label label, string str);
F_frag F_ProcFrag(T_stm body, F_frame frame);

typedef struct F_fragList_ *F_fragList;
struct F_fragList_ 
{
	F_frag head; 
	F_fragList tail;
};

F_fragList F_FragList(F_frag head, F_fragList tail);

T_exp F_externalCall(string s, T_expList args);

Temp_map F_tempMap;
Temp_tempList F_registers();
string F_getlabel(F_frame frame);
T_exp F_Exp(F_access acc, T_exp framePtr);
Temp_label F_name(F_frame f);
F_accessList F_formals(F_frame f);
F_access F_allocLocal(F_frame f, bool escape);
F_accessList bool2access(U_boolList formals);
extern const int F_wordSize;
Temp_temp F_RBP();
Temp_temp F_RSP();
Temp_temp F_RAX();
Temp_temp F_RBX();
Temp_temp F_RDI();
Temp_temp F_RSI();
Temp_temp F_RDX();
Temp_temp F_RCX();
Temp_temp F_R8();
Temp_temp F_R9();
Temp_temp F_R10();
Temp_temp F_R11();
Temp_temp F_R12();
Temp_temp F_R13();
Temp_temp F_R14();
Temp_temp F_R15();
Temp_temp F_FKE();
Temp_tempList F_calldefs();
Temp_tempList F_hardRegs();
int F_spill(F_frame f);

string Temp_tempName(Temp_temp t);

int F_size(F_frame f);

void F_saveSpill(F_frame f, Temp_temp t, F_access ac);
int F_loadSpill(F_frame f, Temp_temp t);

#endif
