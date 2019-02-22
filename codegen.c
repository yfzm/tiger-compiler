#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"


static Temp_temp munchExp(T_exp e);
static void munchStm(T_stm s);
static Temp_tempList munchArgs(T_expList args);

static AS_instrList iList = NULL, last = NULL;
static void emit(AS_instr inst) {
    if (last != NULL) {
        last = last->tail = AS_InstrList(inst, NULL);
    } else {
        last = iList = AS_InstrList(inst, NULL);
    }
}

Temp_tempList L(Temp_temp h, Temp_tempList t) {
    return Temp_TempList(h, t);
}

static Temp_temp munchExp(T_exp e) {
    char *inst = (char*) checked_malloc(MAXLINE);
    switch (e->kind) {
        case T_MEM: {
            Temp_temp r = Temp_newtemp();
            if (e->u.MEM->kind == T_BINOP && e->u.MEM->u.BINOP.op == T_plus &&
              (e->u.MEM->u.BINOP.left->kind == T_CONST || e->u.MEM->u.BINOP.right->kind == T_CONST)) {
                Temp_temp s;
                int c = 0;
                if (e->u.MEM->u.BINOP.left->kind == T_CONST) {
                    s = munchExp(e->u.MEM->u.BINOP.right);
                    c = e->u.MEM->u.BINOP.left->u.CONST;
                } else /*(e->u.MEM->u.BINOP.right->kind == T_CONST)*/ {
                    s = munchExp(e->u.MEM->u.BINOP.left);
                    c = e->u.MEM->u.BINOP.right->u.CONST;
                }
                sprintf(inst, "movq %d(`s0), `d0", c);
                emit(AS_Oper(inst, L(r, NULL), L(s, NULL), NULL));
                return r;
            }
            if (e->u.MEM->kind == T_CONST) {
                sprintf(inst, "movq $%d, `d0", e->u.MEM->u.CONST);
                emit(AS_Oper(inst, L(r, NULL), NULL, NULL));
                return r;
            }
            emit(AS_Oper("movq (`s0), `d0", L(r, NULL), L(munchExp(e->u.MEM), NULL), NULL));
            return r;
        }
        case T_BINOP: {
            Temp_temp r = Temp_newtemp();
            if (e->u.BINOP.op == T_plus && e->u.BINOP.left->kind == T_CONST) {
                sprintf(inst, "leaq %d(`s0), `d0", e->u.BINOP.left->u.CONST);
                emit(AS_Oper(inst, L(r, NULL), L(munchExp(e->u.BINOP.right), NULL), NULL));
                return r;
            }
            if (e->u.BINOP.op == T_plus && e->u.BINOP.right->kind == T_CONST) {
                sprintf(inst, "leaq %d(`s0), `d0", e->u.BINOP.right->u.CONST);
                emit(AS_Oper(inst, L(r, NULL), L(munchExp(e->u.BINOP.left), NULL), NULL));
                return r;
            }
            
            Temp_temp a = munchExp(e->u.BINOP.left);
            Temp_temp b = munchExp(e->u.BINOP.right);
            emit(AS_Move("movq `s0, `d0", L(r, NULL), L(a, NULL)));
            switch (e->u.BINOP.op) {

                case T_plus: 
                    emit(AS_Oper("addq `s0, `d0", L(r, NULL), L(b, L(r, NULL)), NULL));
                    break;
                case T_minus: 
                    emit(AS_Oper("subq `s0, `d0", L(r, NULL), L(b, L(r, NULL)), NULL));
                    break;
                case T_mul: 
                    emit(AS_Oper("imulq `s0, `d0", L(r, NULL), L(b, L(r, NULL)), NULL));
                    break;
                case T_div: {
                    emit(AS_Move("movq `s0, `d0", L(F_RAX(), NULL), L(a, NULL)));
                    emit(AS_Oper("cqto", L(F_RDX(), L(F_RAX(), NULL)), L(F_RAX(), NULL), NULL));
                    emit(AS_Oper("idivq `s0", L(F_RDX(), L(F_RAX(), NULL)), L(b, L(F_RDX(), L(F_RAX(), NULL))), NULL));
                    emit(AS_Move("movq `s0, `d0", L(r, NULL), L(F_RAX(), NULL)));
                    break;
                }
                default:
                    assert(0);
            }
            return r;
        }
        case T_CALL: {
            assert(e->u.CALL.fun->kind == T_NAME);
            // Temp_temp rdi_bk = Temp_newtemp();
            // Temp_temp rsi_bk = Temp_newtemp();
            // Temp_temp rdx_bk = Temp_newtemp();
            // Temp_temp rcx_bk = Temp_newtemp();
            // Temp_temp rax_bk = Temp_newtemp();
            // Temp_temp r8_bk = Temp_newtemp();
            // Temp_temp r9_bk = Temp_newtemp();
            // Temp_temp r10_bk = Temp_newtemp();
            // Temp_temp r11_bk = Temp_newtemp();
            // emit(AS_Move("movq `s0, `d0", L(rdi_bk, NULL), L(F_RDI(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(rsi_bk, NULL), L(F_RSI(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(rdx_bk, NULL), L(F_RDX(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(rcx_bk, NULL), L(F_RCX(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(rax_bk, NULL), L(F_RAX(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(r8_bk, NULL), L(F_R8(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(r9_bk, NULL), L(F_R9(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(r10_bk, NULL), L(F_R10(), NULL)));
            // emit(AS_Move("movq `s0, `d0", L(r11_bk, NULL), L(F_R11(), NULL)));
            

            Temp_temp r = Temp_newtemp();
            // Temp_temp s = munchExp(e->u.CALL.fun);
            T_expList reversedArgList = T_reverseList(e->u.CALL.args);
            Temp_tempList l = munchArgs(reversedArgList);
            sprintf(inst, "callq %s", Temp_labelstring(e->u.CALL.fun->u.NAME));
            emit(AS_Oper(inst, F_calldefs(), NULL, NULL));
            emit(AS_Move("movq %rax, `d0", L(r, NULL), L(F_RAX(), NULL)));

            int argCount = T_listCount(reversedArgList);
            if (argCount > 6) {
                inst = checked_malloc(MAXLINE);
                sprintf(inst, "addq $%d, %%rsp", (argCount - 6) * F_wordSize);
                emit(AS_Oper(inst, L(F_RSP(), NULL), L(F_RSP(), NULL), NULL));
            }
            // emit(AS_Move("movq `s0, `d0", L(F_RDI(), NULL), L(rdi_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_RSI(), NULL), L(rsi_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_RDX(), NULL), L(rdx_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_RCX(), NULL), L(rcx_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_RAX(), NULL), L(rax_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_R8(), NULL), L(r8_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_R9(), NULL), L(r9_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_R10(), NULL), L(r10_bk, NULL)));
            // emit(AS_Move("movq `s0, `d0", L(F_R11(), NULL), L(r11_bk, NULL)));
            return r;
        }
        case T_CONST: {
            Temp_temp r = Temp_newtemp();
            sprintf(inst, "movq $%d, `d0", e->u.CONST);
            emit(AS_Oper(inst, L(r, NULL), NULL, NULL));
            return r;
        }
        case T_NAME: { //???
            Temp_temp r = Temp_newtemp();
            sprintf(inst, "movq $.%s, `d0", Temp_labelstring(e->u.NAME));
            emit(AS_Oper(inst, L(r, NULL), NULL, NULL));
            return r;
        }
        case T_ESEQ: {
            munchStm(e->u.ESEQ.stm);
            return munchExp(e->u.ESEQ.exp);
        }
        case T_TEMP: {
            return e->u.TEMP;
        }
        assert(0);
    }
}

static void munchStm(T_stm s) {
    char *inst = (char*) checked_malloc(MAXLINE);
    switch (s->kind) {
        case T_MOVE: {
            if (s->u.MOVE.dst->kind == T_MEM) {
                Temp_temp src = munchExp(s->u.MOVE.src);
                T_exp movStm = s->u.MOVE.dst->u.MEM;
                if (movStm->kind == T_BINOP && movStm->u.BINOP.op == T_plus &&
                  (movStm->u.BINOP.left->kind == T_CONST || movStm->u.BINOP.right->kind == T_CONST)) {
                    Temp_temp t;
                    int c = 0;
                    if (movStm->u.BINOP.left->kind == T_CONST) {
                        t = munchExp(movStm->u.BINOP.right);
                        c = movStm->u.BINOP.left->u.CONST;
                    } else /*(movStm->u.BINOP.right->kind == T_CONST)*/ {
                        t = munchExp(movStm->u.BINOP.left);
                        c = movStm->u.BINOP.right->u.CONST;
                    }
                    sprintf(inst, "movq `s0, %d(`s1)", c);
                    emit(AS_Oper(inst, NULL, L(src, L(t, NULL)), NULL));
                    break;
                }
                Temp_temp dst = munchExp(s->u.MOVE.dst->u.MEM);
                emit(AS_Oper("movq `s0, (`s1)", NULL, L(src, L(dst, NULL)), NULL));
                break;
            } else if (s->u.MOVE.dst->kind == T_TEMP) {
                Temp_temp dst = munchExp(s->u.MOVE.dst);
                if (s->u.MOVE.src->kind == T_CONST) {
                    sprintf(inst, "movq $%d, `d0", s->u.MOVE.src->u.CONST);
                    emit(AS_Oper(inst, L(dst, NULL), NULL, NULL));
                    break;
                }
                if (s->u.MOVE.src->kind == T_NAME) {
                    sprintf(inst, "movq $.%s, `d0", Temp_labelstring(s->u.MOVE.src->u.NAME));
                    emit(AS_Oper(inst, L(dst, NULL), NULL, NULL));
                    break;
                }
                Temp_temp src = munchExp(s->u.MOVE.src);
                emit(AS_Move("movq `s0, `d0", L(dst, NULL), L(src, NULL)));
                break;
            } else {
                assert(0);
            }
        }
        case T_LABEL: {
            sprintf(inst, ".%s", Temp_labelstring(s->u.LABEL));
            emit(AS_Label(inst, s->u.LABEL));
            break;
        }
        case T_SEQ: {
            munchStm(s->u.SEQ.left);
            munchStm(s->u.SEQ.right);
            break;
        }
        case T_JUMP: {
            assert (s->u.JUMP.exp->kind == T_NAME);
            sprintf(inst, "jmp .%s", Temp_labelstring(s->u.JUMP.exp->u.NAME));
            emit(AS_Oper(inst, NULL, NULL, AS_Targets(s->u.JUMP.jumps)));
            break;
        }
        case T_CJUMP: {
            Temp_temp a = munchExp(s->u.CJUMP.left);
            Temp_temp b = munchExp(s->u.CJUMP.right);
            emit(AS_Oper("cmp `s0, `s1", NULL, L(b, L(a, NULL)), NULL));
            switch (s->u.CJUMP.op) {
                case T_eq: {
                    sprintf(inst, "je .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                case T_ne: {
                    sprintf(inst, "jne .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                case T_le: {
                    sprintf(inst, "jle .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                case T_lt: {
                    sprintf(inst, "jl .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                case T_ge: {
                    sprintf(inst, "jge .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                case T_gt: {
                    sprintf(inst, "jg .%s", Temp_labelstring(s->u.CJUMP.true));
                    break;
                }
                default: {
                    assert(0);
                }
            }
            emit(AS_Oper(inst, NULL, NULL, AS_Targets(Temp_LabelList(s->u.CJUMP.true, NULL))));
            break;
        }
        case T_EXP: {
            munchExp(s->u.EXP);
            break;
        }
        assert(0);
    }
}

// assume the args are already in reverse order
static Temp_tempList munchArgs(T_expList args) {
    Temp_tempList l = NULL;
    int count = T_listCount(args) - 1;
    while (count >= 0) {
        char *inst = (char*) checked_malloc(MAXLINE);
        Temp_temp s = munchExp(args->head);
        l = Temp_TempList(s, l);
        switch (count) {
            case 0: 
                emit(AS_Move("movq `s0, %rdi", L(F_RDI(), NULL), L(s, NULL)));
                break;
            case 1: 
                emit(AS_Move("movq `s0, %rsi", L(F_RSI(), NULL), L(s, NULL)));
                break;
            case 2: 
                emit(AS_Move("movq `s0, %rdx", L(F_RDX(), NULL), L(s, NULL)));
                break;
            case 3: 
                emit(AS_Move("movq `s0, %rcx", L(F_RCX(), NULL), L(s, NULL)));
                break;
            case 4: 
                emit(AS_Move("movq `s0, %r8", L(F_R8(), NULL), L(s, NULL)));
                break;
            case 5: 
                emit(AS_Move("movq `s0, %r9", L(F_R9(), NULL), L(s, NULL)));
                break;
            default: 
                emit(AS_Oper("pushq `s0", NULL, L(s, NULL), NULL));
                break;

        }
        args = args->tail;
        count--;
    }
    return l;
}


AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    AS_instrList list;
    T_stmList sl;

    Temp_temp rbx_bk = Temp_newtemp();
    Temp_temp r12_bk = Temp_newtemp();
    Temp_temp r13_bk = Temp_newtemp();
    Temp_temp r14_bk = Temp_newtemp();
    Temp_temp r15_bk = Temp_newtemp();
    Temp_temp rbp_bk = Temp_newtemp();

    emit(AS_Move("movq `s0, `d0", L(rbx_bk, NULL), L(F_RBX(), NULL)));
    emit(AS_Move("movq `s0, `d0", L(r12_bk, NULL), L(F_R12(), NULL)));
    emit(AS_Move("movq `s0, `d0", L(r13_bk, NULL), L(F_R13(), NULL)));
    emit(AS_Move("movq `s0, `d0", L(r14_bk, NULL), L(F_R14(), NULL)));
    emit(AS_Move("movq `s0, `d0", L(r15_bk, NULL), L(F_R15(), NULL)));
    emit(AS_Move("movq `s0, `d0", L(rbp_bk, NULL), L(F_RBP(), NULL)));

    for (sl = stmList; sl; sl = sl->tail) {
        munchStm(sl->head);
    }

    emit(AS_Move("movq `s0, `d0", L(F_RBP(), NULL), L(rbp_bk, NULL)));
    emit(AS_Move("movq `s0, `d0", L(F_R15(), NULL), L(r15_bk, NULL)));
    emit(AS_Move("movq `s0, `d0", L(F_R14(), NULL), L(r14_bk, NULL)));
    emit(AS_Move("movq `s0, `d0", L(F_R13(), NULL), L(r13_bk, NULL)));
    emit(AS_Move("movq `s0, `d0", L(F_R12(), NULL), L(r12_bk, NULL)));
    emit(AS_Move("movq `s0, `d0", L(F_RBX(), NULL), L(rbx_bk, NULL)));

    list = iList;
    iList = last = NULL;
    return list;
}
