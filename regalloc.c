#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"
#include "codegen.h"
#include "string.h"

Temp_tempList AS_def(AS_instr inst) {
	switch (inst->kind) {
		case I_OPER: {
			return inst->u.OPER.dst;
		}
		case I_MOVE: {
			return inst->u.MOVE.dst;
		}
		case I_LABEL: {
			return NULL;
		}
	}
	assert(0);
}

Temp_tempList AS_use(AS_instr inst) {
	switch (inst->kind) {
		case I_OPER: {
			return inst->u.OPER.src;
		}
		case I_MOVE: {
			return inst->u.MOVE.src;
		}
		case I_LABEL: {
			return NULL;
		}
	}
	assert(0);
}

void Temp_replaceTemp(Temp_tempList *ptl, Temp_temp old, Temp_temp anew) {
	Temp_tempList tl = *ptl;
	
	for (; tl; tl = tl->tail) {
		if (tl->head == old) {
			tl->head = anew;
			// *ptl = Temp_TempList(anew, tl);
		}
	}
}

static void rewriteProgram(Temp_tempList spills, F_frame f, AS_instrList *pil) {
	AS_instrList il = *pil;
	// int off = 0;
	for (; spills; spills = spills->tail) {
		Temp_temp cur = spills->head;
		// off = F_spill(f);  // ??? Change size!!!!
		AS_instrList pre = NULL;
		for (AS_instrList l = il; l; l = l->tail) {
			Temp_tempList def = AS_def(l->head);
			Temp_tempList use = AS_use(l->head);
			if (use && List_inList(cur, use)) {
				Temp_temp t = Temp_newtemp();
				Temp_replaceTemp(&use, cur, t);
				use = Temp_TempList(t, use);
				char *inst = checked_malloc(MAXLINE);

				sprintf(inst, "movq %d(%%rsp), `d0", F_loadSpill(f, cur));
				// sprintf(inst, "popq `d0");
				AS_instrList new_il = AS_InstrList(AS_Oper(inst, L(t, NULL), NULL, NULL), l);
				if (pre == NULL) {
					il = new_il;
				} else {
					pre->tail = new_il;
				}
			}
			if (def && List_inList(cur, def)) {
				Temp_temp t = Temp_newtemp();
				Temp_replaceTemp(&def, cur, t);
				char *inst = checked_malloc(MAXLINE);

				int off = F_size(f);
				F_access acc = F_allocLocal(f, TRUE);
				F_saveSpill(f, cur, acc);

				sprintf(inst, "movq `s0, %d(%%rsp)", off);
				// sprintf(inst, "pushq `s0");
				l->tail = AS_InstrList(AS_Oper(inst, NULL, L(t, NULL), NULL), l->tail);
				l = l->tail;
			}
			pre = l;
		}
	}
	*pil = il;
}

void cleanCode(AS_instrList *pil, Temp_map tm) {
	AS_instrList il = *pil;
	AS_instrList last = NULL;
	AS_instrList lastValid = NULL;  // Sometimes last would be deleted
	while (il) {
		AS_instr instr = il->head;
		if (instr->kind == I_MOVE) {
			char *src = Temp_look(tm, instr->u.MOVE.src->head);
			char *dst = Temp_look(tm, instr->u.MOVE.dst->head);
			if (!strncmp(src, dst, 4)) {
				if (last) {
					last->tail = il->tail;
				} else {
					*pil = il->tail;
				}
			} else {
				last = il;
			}
		} else if (instr->kind == I_OPER) {
			if (!strncmp(instr->u.OPER.assem, "jmp", 3)) {
				Temp_label to = instr->u.OPER.jumps->labels->head;
				if (il->tail && il->tail->head->kind == I_LABEL &&
					il->tail->head->u.LABEL.label == to) {
					if (last) {
						last->tail = il->tail;
					} else {
						*pil = il->tail;
					}
				} else {
					last = il;
				}
			} else {
				last = il;
			}
		} else {
			last = il;
		}
		// last = il;
		il = il->tail;
	}
}

void fke2rsp(AS_instrList *pil, int frameSize, Temp_map tm) {
	for (AS_instrList il = *pil; il; il = il->tail) {
		AS_instr instr = il->head;
		if (instr->kind != I_OPER || instr->u.OPER.src == NULL) {
			continue;
		}
		char *assem = instr->u.OPER.assem;
		char *src = Temp_look(tm, instr->u.OPER.src->head);
		if (!strncmp(src, "%fke", 4)) {
			assert(!strncmp(assem, "movq", 4));
			int num = atoi(assem+5);
			assert(num >= 0);
			char *newassem = checked_malloc(MAXLINE);
			sprintf(newassem, "movq %d(`s0), `d0", num + frameSize);
			instr->u.OPER.assem = newassem;
			instr->u.OPER.src = L(F_RSP(), NULL);
			// instr->u.OPER.dst = L(F_RSP(), NULL);
		}

	}
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	static int count = 0;
	if (count >= 100) {
		struct RA_result ret;
		return ret;
	}
	count++;

	G_graph flow_graph = FG_AssemFlowGraph(il, f);
	struct Live_graph lg = Live_liveness(flow_graph);

	struct COL_result result = COL_color(lg, F_tempMap, F_hardRegs());
	if (result.spills) {
		printf("\n");
		printf(".............................................................................\n");
		printf(".............................................................................\n");
		printf("...................................REWRITE...................................\n");
		printf(".............................................................................\n");
		printf(".............................................................................\n");
		printf("\n");
		rewriteProgram(result.spills, f, &il);
		return RA_regAlloc(f, il);
	}

	cleanCode(&il, result.coloring);
	fke2rsp(&il, F_size(f), result.coloring);

	struct RA_result ret;
	ret.il = il;
	ret.coloring = result.coloring;

	return ret;
}
