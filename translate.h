#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_expList_ *Tr_expList;

Tr_expList Tr_ExpList(Tr_exp, Tr_expList);

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;

typedef struct Tr_level_ *Tr_level;

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_access Tr_getAccess(Tr_accessList);

Tr_accessList Tr_getNextAccess(Tr_accessList);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);

F_fragList Tr_getResult(void);

Tr_exp Tr_noExp();
Tr_exp Tr_simpleVar(Tr_access, Tr_level);
Tr_exp Tr_filedVar(Tr_exp base, int index);
Tr_exp Tr_subscriptVar(Tr_exp, Tr_exp);

Tr_exp Tr_nilExp();
Tr_exp Tr_intExp(int);
Tr_exp Tr_stringExp(string);
Tr_exp Tr_callExp(Tr_level caller, Tr_level callee, Temp_label func, Tr_expList args);
Tr_exp Tr_opExp(A_oper, Tr_exp, Tr_exp);
Tr_exp Tr_recordExp(Tr_expList);
Tr_exp Tr_seqExp(Tr_exp first, Tr_exp second);
Tr_exp Tr_assignExp(Tr_exp, Tr_exp);
Tr_exp Tr_ifExp(Tr_exp condition, Tr_exp then, Tr_exp elsee);
Tr_exp Tr_whileExp(Tr_exp condition, Tr_exp body, Temp_label done);
Tr_exp Tr_forExp(Tr_access, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done);
Tr_exp Tr_jump(Temp_label label);
//Tr_exp Tr_letExp();
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init);
Tr_exp Tr_strEqual(Tr_exp left, Tr_exp right);

Tr_expList Tr_reverseList(Tr_expList el);

#endif
