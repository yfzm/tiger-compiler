#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
	AS_instr instr = G_nodeInfo(n);
	switch (instr->kind) {
		case I_OPER:
			return instr->u.OPER.dst;
		case I_MOVE:
			return instr->u.MOVE.dst;
		case I_LABEL:
			return NULL;
	}
	assert(0);
}

Temp_tempList FG_use(G_node n) {
	AS_instr instr = G_nodeInfo(n);
	switch (instr->kind) {
		case I_OPER:
			return instr->u.OPER.src;
		case I_MOVE:
			return instr->u.MOVE.src;
		case I_LABEL:
			return NULL;
	}
	assert(0);
}

bool FG_isMove(G_node n) {
	AS_instr instr = G_nodeInfo(n);
	return instr->kind == I_MOVE;
}

static bool isDirectJump(string assem) {
	if (!strncmp(assem, "jmp", 3)) 
		return TRUE;
	return FALSE;
}

void show_flowgraph(void *info) {
	AS_instr instr = info;
	fprintf(stdout, "info: %s", instr->u.OPER.assem);
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	G_graph graph = G_Graph();
	TAB_table label2node = TAB_empty();
	G_node last = NULL;
	AS_instr last_instr = NULL;
	for (AS_instrList cur = il; cur; cur = cur->tail) {
		G_node node = G_Node(graph, cur->head);
		if (last && !(last_instr && last_instr->kind == I_OPER && isDirectJump(last_instr->u.OPER.assem))) {
			G_addEdge(last, node);
		}
		if (cur->head->kind == I_LABEL) {
			TAB_enter(label2node, cur->head->u.LABEL.label, node);
		}
		last = node;
		last_instr = cur->head;
		// printf("\n");
		// G_show(stdout, G_nodes(graph), show_flowgraph);
	}
	for (G_nodeList nl = G_nodes(graph); nl; nl = nl->tail) {
		AS_instr instr = G_nodeInfo(nl->head);
		if (instr->kind == I_OPER && instr->u.OPER.jumps) {
			for (Temp_labelList ll = instr->u.OPER.jumps->labels; ll; ll = ll->tail) {
				G_node label_node = TAB_look(label2node, ll->head);
				G_addEdge(nl->head, label_node);
			}
		}
	}
	G_show(stdout, G_nodes(graph), show_flowgraph);
	return graph;
}
