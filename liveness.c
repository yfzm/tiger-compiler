#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"


G_node getNodeFromTemp(Temp_temp item, TAB_table tab, G_graph graph);

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}


Temp_temp Live_gtemp(G_node n) {
	return G_nodeInfo(n);
}

Temp_tempList List_Union(Temp_tempList a, Temp_tempList b) {
	Temp_tempList r = a;
	for (; b; b = b->tail) {
		if (!List_inList(b->head, a)) {
			r = Temp_TempList(b->head, r);
		}
	}
	return r;
}


Temp_tempList List_Diff(Temp_tempList a, Temp_tempList b) {
	Temp_tempList r = NULL;
	for (; a; a = a->tail) {
		if (!List_inList(a->head, b)) {
			r = Temp_TempList(a->head, r);
		}
	}
	return r;
}

bool List_inList(Temp_temp item, Temp_tempList list) {
	for (; list; list = list->tail) {
		if (item == list->head) {
			return TRUE;
		}
	}
	return FALSE;
}

bool inMoveList(G_node src, G_node dst, Live_moveList ml) {
	for (; ml; ml = ml->tail) {
		if (src == ml->src && dst == ml->dst) {
			return TRUE;
		}
	}
	return FALSE;
}

bool List_Equal(Temp_tempList a, Temp_tempList b) {
	Temp_tempList ta = NULL, tb = NULL;
	for (ta = a, tb = b; ta && tb; ta = ta->tail, tb = tb->tail) {
		if (!List_inList(ta->head, b)) {
			return FALSE;
		}
		if (!List_inList(tb->head, a)) {
			return FALSE;
		}
	}
	return ta == NULL && tb == NULL;
}

G_node getNodeFromTemp(Temp_temp item, TAB_table tab, G_graph graph) {
	G_node node = TAB_look(tab, item);
	if (node == NULL) {
		node = G_Node(graph, item);
		TAB_enter(tab, item, node);
	}
	assert(node != NULL);
	return node;
}

void showInterferenceGraphInfo(void *info) {
	Temp_temp t = info;
	fprintf(stdout, "\nNode: temp:%d(%s)\n", Temp_int(t), Temp_tempName(t));
}

void Live_showMoveList(Live_moveList ml) {
	while (ml) {
		Temp_temp src = Live_gtemp(ml->src);
		Temp_temp dst = Live_gtemp(ml->dst);
		int key_src = G_nodeKey(ml->src);
		int key_dst = G_nodeKey(ml->dst);
		printf("(%d,%d,%s) -> (%d,%d,%s)\n", key_src, Temp_int(src), Temp_tempName(src), key_dst, Temp_int(dst), Temp_tempName(dst));
		ml = ml->tail;
	}
}

int Live_mllen(Live_moveList ml) {
	int count = 0;
	while (ml) {
		count++;
		ml = ml->tail;
	}
	return count;
}

struct Live_graph Live_liveness(G_graph flow) {
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;

	// calculate liveMap
	G_table in = G_empty();
	G_table out = G_empty();
	bool stable = FALSE;
	while (!stable) {
		stable = TRUE;
		for (G_nodeList nl = G_nodes(flow); nl; nl = nl->tail) {
			AS_instr instr = G_nodeInfo(nl->head);
			Temp_tempList def = FG_def(nl->head);
			Temp_tempList use = FG_use(nl->head);
			Temp_tempList in_set = G_look(in, nl->head);
			Temp_tempList out_set = G_look(out, nl->head);

			Temp_tempList new_in_set = List_Union(use, List_Diff(out_set, def));
			Temp_tempList new_out_set = NULL;
			for (G_nodeList succ_list = G_succ(nl->head); succ_list; succ_list = succ_list->tail) {
				new_out_set = List_Union(new_out_set, G_look(in, succ_list->head));
			}

			if (!List_Equal(in_set, new_in_set)) {
				stable = FALSE;
				G_enter(in, nl->head, new_in_set);
			}
			if (!List_Equal(out_set, new_out_set)) {
				stable = FALSE;
				G_enter(out, nl->head, new_out_set);
			}
		}
	}

	TAB_table temp2node = TAB_empty();
	// add hard register to interference graph
	for (Temp_tempList a = F_hardRegs(); a; a = a->tail) {
		for (Temp_tempList b = a->tail; b; b = b->tail) {
			G_node na = getNodeFromTemp(a->head, temp2node, lg.graph);
			G_node nb = getNodeFromTemp(b->head, temp2node, lg.graph);
			G_addEdge(na, nb);
			G_addEdge(nb, na);
		}
	}

	// MAIN
	for (G_nodeList nl = G_nodes(flow); nl; nl = nl->tail) {
		Temp_tempList liveouts = G_look(out, nl->head);
		bool isMove = FG_isMove(nl->head);

		for (Temp_tempList def = FG_def(nl->head); def; def = def->tail) {
			if (def->head == F_RSP()) {
				continue;
			}
			Temp_tempList use = FG_use(nl->head);
			G_node na = getNodeFromTemp(def->head, temp2node, lg.graph);
			// add into interference graph
			for (Temp_tempList out_set = TAB_look(out, nl->head); out_set; out_set = out_set->tail) {
				if (out_set->head == F_RSP() || out_set->head == def->head) {
					continue;
				}
				// if isMove, node in use_set shouldn't be added to interference graph
				if (isMove && List_inList(out_set->head, use)) {
					continue;
				}
				G_node nb = getNodeFromTemp(out_set->head, temp2node, lg.graph);
				G_addEdge(na, nb);
				G_addEdge(nb, na);
			}
			// add into movelist
			if (isMove) {
				for (Temp_tempList use_set = use; use_set; use_set = use_set->tail) {
					if (use_set->head == F_RSP() || use_set->head == def->head) {
						continue;
					}
					G_node nb = getNodeFromTemp(use_set->head, temp2node, lg.graph);
					if (!inMoveList(nb, na, lg.moves)) {
						lg.moves = Live_MoveList(nb, na, lg.moves);
					}
				}
			}
		}
	}

	G_show(stdout, G_nodes(lg.graph), showInterferenceGraphInfo);
	Live_showMoveList(lg.moves);
	return lg;
}


