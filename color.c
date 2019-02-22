#include <stdio.h>
#include <string.h>

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
#include "table.h"

#define K 15

static string reg_name[K] = {"%rax", "%rbx", "%rcx", "%rdx",
	"%rsi", "%rdi", "%r8", "%r9", "%r10",
	"%r11", "%r12", "%r13", "%r14", "%r15", "%rbp"};

// static G_nodeList precolored;
static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;
static G_nodeList spillWorklist;
static G_nodeList spilledNodes;
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
static G_nodeList selectStack;

static Live_moveList coalescedMoves;
static Live_moveList constrainedMoves;
static Live_moveList frozenMoves;
static Live_moveList worklistMoves;
static Live_moveList activeMoves;

static bool *adjSet;
static G_graph graph;
static G_table alias;
static G_table degree;
static G_table color;
static int nodeCount;

static void build(struct Live_graph lg, Temp_map initial, Temp_tempList regs);
static void addEdge(G_node u, G_node v);
static void makeWorklist();
static G_nodeList adjacent(G_node n);
static Live_moveList nodeMoves(G_node n);
static bool moveRelated(G_node node);
static void simplify();
static void decrementDegree(G_node n);
static void enableMoves(G_nodeList nodes);
static void coalesce();
static void addWorkList(G_node n);
static bool ok(G_node u, G_node v);
static bool conservative(G_nodeList nl);
static G_node getAlias(G_node node);
static void combine(G_node u, G_node v);
static void freeze();
static void freezeMoves(G_node u);
static void selectSpill();
static void assignColors();

static void buildColorAndDegree(Temp_map init);
static void buildAdjSet();
static bool inAdjSet(G_node u, G_node v);
static void addToAdjSet(G_node u, G_node v);  // both way
static G_nodeList G_DiffNodeList(G_nodeList a, G_nodeList b);
static G_nodeList G_UnionNodeList(G_nodeList a, G_nodeList b);
static bool nodeEqual(G_node u, G_node v);
static Live_moveList Live_DiffMoveList(Live_moveList a, Live_moveList b);
static Live_moveList Live_UnionMoveList(Live_moveList a, Live_moveList b);
static bool Live_inMoveList(G_node src, G_node dst, Live_moveList ml);
static bool inColor(G_node n);

// static string reg_name[K] = {"rax", "rbx", "rcx", "rdx",
// 	"rsi", "rdi", "r8", "r9", "r10",
// 	"r11", "r12", "r13", "r14", "r15"};

static void buildColorAndDegree(Temp_map init) {
	for (G_nodeList nl = G_nodes(graph); nl; nl = nl->tail) {
		Temp_temp t = Live_gtemp(nl->head);
		int tc = -1;
		if (t == F_RAX()) {
			tc = 0;
		} else if (t == F_RBX()) {
			tc = 1;
		} else if (t == F_RCX()) {
			tc = 2;
		} else if (t == F_RDX()) {
			tc = 3;
		} else if (t == F_RSI()) {
			tc = 4;
		} else if (t == F_RDI()) {
			tc = 5;
		} else if (t == F_R8()) {
			tc = 6;
		} else if (t == F_R9()) {
			tc = 7;
		} else if (t == F_R10()) {
			tc = 8;
		} else if (t == F_R11()) {
			tc = 9;
		} else if (t == F_R12()) {
			tc = 10;
		} else if (t == F_R13()) {
			tc = 11;
		} else if (t == F_R14()) {
			tc = 12;
		} else if (t == F_R15()) {
			tc = 13;
		} else if (t == F_RBP()) {
			tc = 14;
		}
		if (tc != -1) {
			int *c = checked_malloc(sizeof(int));
			*c = tc;
			G_enter(color, nl->head, c);
		}
		int *d = checked_malloc(sizeof(int));
		*d = outDegree(nl->head);
		G_enter(degree, nl->head, d);
	}
}

static void buildAdjSet() {
	for (G_nodeList nl = G_nodes(graph); nl; nl = nl->tail) {
		G_node a = nl->head;
		for (G_nodeList nnl = G_succ(a); nnl; nnl = nnl->tail) {
			G_node b = nnl->head;
			if (a != b) {
				// adjSet[G_nodeKey(a) * nodeCount + G_nodeKey(b)] = TRUE;
				addToAdjSet(a, b);
			}
		}
	}
}

static bool inAdjSet(G_node u, G_node v) {
	return adjSet[G_nodeKey(u) * nodeCount + G_nodeKey(v)];
}

static void addToAdjSet(G_node u, G_node v) {
	int uk = G_nodeKey(u);
	int vk = G_nodeKey(v);
	adjSet[uk * nodeCount + vk] = TRUE;
	adjSet[vk * nodeCount + uk] = TRUE;
}

static G_nodeList G_DiffNodeList(G_nodeList a, G_nodeList b) {
	G_nodeList r = NULL;
	for (; a; a = a->tail) {
		if (!G_inNodeList(a->head, b)) {
			r = G_NodeList(a->head, r);
		}
	}
	return r;
}

static G_nodeList G_UnionNodeList(G_nodeList a, G_nodeList b) {
	G_nodeList r = a;
	for (; b; b = b->tail) {
		if (!G_inNodeList(b->head, a)) {
			r = G_NodeList(b->head, r);
		}
	}
	return r;
}

static bool nodeEqual(G_node u, G_node v) {
	return getAlias(u) == getAlias(v);
}

static Live_moveList Live_DiffMoveList(Live_moveList a, Live_moveList b) {
	Live_moveList r = NULL;
	for (; a; a = a->tail) {
		if (!Live_inMoveList(a->src, a->dst, b)) {
			r = Live_MoveList(a->src, a->dst, r);
		}
	}
	return r;
}

static Live_moveList Live_UnionMoveList(Live_moveList a, Live_moveList b) {
	Live_moveList r = a;
	for (; b; b = b->tail) {
		if (!Live_inMoveList(b->src, b->dst, a)) {
			r = Live_MoveList(b->src, b->dst, r);
		}
	}
	return r;
}

static bool Live_inMoveList(G_node src, G_node dst, Live_moveList list) {
	for (; list; list = list->tail) {
		if (src == list->src && dst == list->dst) {
			return TRUE;
		}
	}
	return FALSE;
}

static bool inColor(G_node n) {
	int *c = G_look(color, n);
	// if (c == NULL) return FALSE;
	return c != NULL;
}

static void showAdjSet() {
	for (int i = 0; i < nodeCount; i++) {
		for (int j = 0; j < nodeCount; j++) {
			if (adjSet[i * nodeCount + j]) {
				printf("1 ");
			} else {
				printf(". ");
			}
		}
		printf("\n");
	}
}

// **********************************************************************************


static void build(struct Live_graph lg, Temp_map initial, Temp_tempList regs) {
	graph = lg.graph;
	alias = G_empty();
	color = G_empty();
	degree = G_empty();
	buildColorAndDegree(initial);
	
	nodeCount = G_nodeCount(graph);
	int adjSetSize = nodeCount * nodeCount * sizeof(bool);
	adjSet = (bool*) checked_malloc(adjSetSize);
	memset(adjSet, FALSE, adjSetSize);
	buildAdjSet();

	// precolored = setPrecolored();
	simplifyWorklist = NULL;
	freezeWorklist = NULL;
	spillWorklist = NULL;
	spilledNodes = NULL;
	coalescedNodes = NULL;
	coloredNodes = NULL;
	selectStack = NULL;

	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = lg.moves;
	activeMoves = NULL;

}

static void addEdge(G_node u, G_node v) {
	if (u != v && !inAdjSet(u, v)) {
		addToAdjSet(u, v);
		if (!inColor(u)) {
			int *d = G_look(degree, u);
			(*d)++;
			G_addEdge(u, v);
		}
		if (!inColor(v)) {
			int *d = G_look(degree, v);
			(*d)++;
			printf("    addEdge: v: degree: %d\n", *d);
			G_addEdge(v, u);
		}
	}
}

static void makeWorklist() {
	for (G_nodeList nodes = G_nodes(graph); nodes; nodes = nodes->tail) {
		if (Temp_inTempList(Live_gtemp(nodes->head), F_hardRegs())) {
			coloredNodes = G_NodeList(nodes->head, coloredNodes);
		} else {
			int *d = G_look(degree, nodes->head);
			if (*d >= K) {
				spillWorklist = G_NodeList(nodes->head, spillWorklist);
			} else if (moveRelated(nodes->head)) {
				freezeWorklist = G_NodeList(nodes->head, freezeWorklist);
			} else {
				simplifyWorklist = G_NodeList(nodes->head, simplifyWorklist);
			}
		}
	}
}

static G_nodeList adjacent(G_node n) {
	// return G_DiffNodeList(G_succ(n), G_UnionNodeList(selectStack, G_UnionNodeList(coalescedNodes, coloredNodes)));
	return G_DiffNodeList(G_succ(n), G_UnionNodeList(selectStack, coalescedNodes));
}

static Live_moveList nodeMoves(G_node n) {
	Live_moveList ret = NULL;
	for (Live_moveList ml = Live_UnionMoveList(activeMoves, worklistMoves); ml; ml = ml->tail) {
		if (nodeEqual(n, ml->src) || nodeEqual(n, ml->dst)) {
			ret = Live_MoveList(ml->src, ml->dst, ret);
		}
	}
	return ret;
}

static bool moveRelated(G_node node) {
	return nodeMoves(node) != NULL;
}

static void simplify() {
	printf("- - - - - - - - - - - SIMPLIFY BEGIN - - - - - - - - - - -\n");
	G_node node = simplifyWorklist->head;
	simplifyWorklist = simplifyWorklist->tail;
	printf("operate on (%d,%d,%s)\n", G_nodeKey(node), Temp_int(Live_gtemp(node)), Temp_tempName(Live_gtemp(node)));
	selectStack = G_NodeList(node, selectStack);
	for (G_nodeList nl = adjacent(node); nl; nl = nl->tail) {
		decrementDegree(nl->head);
	}
	printf("- - - - - - - - - - - SIMPLIFY END - - - - - - - - - - - -\n");
}

static void decrementDegree(G_node n) {

	if (inColor(n)) return;

	printf("  - - - - - - - - - - - DECREMENT DEGREE BEGIN - - - - - - - - - - -\n");
	printf("  operate on (%d,%d,%s)\n", G_nodeKey(n), Temp_int(Live_gtemp(n)), Temp_tempName(Live_gtemp(n)));
	int *d = G_look(degree, n);
	assert(d && *d != 0);
	printf("  degree: %d -> %d\n", *d, *d - 1);
	(*d)--;
	if (*d == K - 1 && !inColor(n) && G_inNodeList(n, spillWorklist)) {  // ??
		enableMoves(G_NodeList(n, adjacent(n)));
		spillWorklist = G_DiffNodeList(spillWorklist, G_NodeList(n, NULL));
		if (moveRelated(n)) {
			freezeWorklist = G_NodeList(n, freezeWorklist);
		} else {
			simplifyWorklist = G_NodeList(n, simplifyWorklist);
		}
	}
	printf("  - - - - - - - - - - - DECREMENT DEGREE END - - - - - - - - - - - -\n");
}

static void enableMoves(G_nodeList nodes) {
	for (; nodes; nodes = nodes->tail) {
		for (Live_moveList moves = nodeMoves(nodes->head); moves; moves = moves->tail) {
			if (Live_inMoveList(moves->src, moves->dst, activeMoves)) {
				activeMoves = Live_DiffMoveList(activeMoves, Live_MoveList(moves->src, moves->dst, NULL));
				worklistMoves = Live_MoveList(moves->src, moves->dst, worklistMoves);
			}
		}
	}
}

static void coalesce() {
	printf("- - - - - - - - - - - COALESCE BEGIN - - - - - - - - - - -\n");
	G_node x = worklistMoves->src;
	G_node y = worklistMoves->dst;
	G_node u = getAlias(x);
	G_node v = getAlias(y);
	if (inColor(v)) {
		G_node temp = u; u = v; v = temp;
	}
	printf("u: (%d,%d,%s)\nv: (%d,%d,%s)\n", G_nodeKey(u), Temp_int(Live_gtemp(u)), Temp_tempName(Live_gtemp(u)),
											 G_nodeKey(v), Temp_int(Live_gtemp(v)), Temp_tempName(Live_gtemp(v)));
	worklistMoves = worklistMoves->tail;
	if (u == v) {
		printf("CASE1: u==v\n");
		coalescedMoves = Live_MoveList(x, y, coalescedMoves);
		addWorkList(u);
	} else if (inColor(v) || inAdjSet(u, v)) {
		printf("CASE2: u and v are both precolored or it's a constrained move\n");
		constrainedMoves = Live_MoveList(x, y, constrainedMoves);
		addWorkList(u);
		addWorkList(v);
	} else if ((inColor(u) && ok(v, u)) 
			|| (!inColor(u) && conservative(G_UnionNodeList(adjacent(u), adjacent(v))))) {
		printf("CASE3: ready to combine\n");		
		coalescedMoves = Live_MoveList(x, y, coalescedMoves);
		combine(u, v);
		addWorkList(u);
	} else {
		printf("CASE4: send to active move list\n");
		activeMoves = Live_MoveList(x, y, activeMoves);
	}
	printf("- - - - - - - - - - - COALESCE END - - - - - - - - - - - -\n");
}

static void addWorkList(G_node u) {
	int *d = G_look(degree, u);
	if (!inColor(u) && !(moveRelated(u)) && *d < K) {
		freezeWorklist = G_DiffNodeList(freezeWorklist, G_NodeList(u, NULL));
		simplifyWorklist = G_NodeList(u, simplifyWorklist);
	}
}

// v is precolored node
static bool ok(G_node u, G_node v) {
	for (G_nodeList nl = adjacent(u); nl; nl = nl->tail) {
		int *d = G_look(degree, nl->head);
		if (!(*d < K || inColor(nl->head) || inAdjSet(nl->head, v) || inAdjSet(v, nl->head))) {
			printf("    ok? no! degree(%d,%d,%s)=%d and inColor=%d\n", G_nodeKey(nl->head), Temp_int(Live_gtemp(nl->head)), Temp_tempName(Live_gtemp(nl->head)), *d, (inColor(nl->head) ? 1 : 0));
			showAdjSet();
			return FALSE;
		}
	}
	return TRUE;
}

static bool conservative(G_nodeList nl) {
	int k = 0;
	for (; nl; nl = nl->tail) {
		if (inColor(nl->head)) {
			k++;
		} else {
			int *d = G_look(degree, nl->head);
			if (*d >= K) {
				k++;
			}
		}
	}
	printf("    conservative? k=%d\n", k);

	return k < K;
}

static G_node getAlias(G_node n) {
	// if (G_inNodeList(n, coloredNodes)) {
		G_node a = G_look(alias, n);
		if (a == NULL) {
			return n;
		}
		assert(a != n);
		return getAlias(a);
	// }
	// return n;
}

static void combine(G_node u, G_node v) {
	printf("  - - - - - - - - - - - COMBINE BEGIN - - - - - - - - - - -\n");
	printf("  (%d,%d,%s) & (%d,%d,%s)\n", G_nodeKey(u), Temp_int(Live_gtemp(u)), Temp_tempName(Live_gtemp(u)),
										G_nodeKey(v), Temp_int(Live_gtemp(v)), Temp_tempName(Live_gtemp(v)));
	if (G_inNodeList(v, freezeWorklist)) {
		freezeWorklist = G_DiffNodeList(freezeWorklist, G_NodeList(v, NULL));
	} else {
		assert(G_inNodeList(v, spillWorklist));
		spillWorklist = G_DiffNodeList(spillWorklist, G_NodeList(v, NULL));
	}
	coalescedNodes = G_NodeList(v, coalescedNodes);
	// setAlias(v, u);  // aliasa[v] <- u
	G_enter(alias, v, u);
	enableMoves(G_NodeList(v, NULL));
	
	int *d0 = G_look(degree, u);
	printf("  Before combine, degree=%d\n", *d0);
	for (G_nodeList nl = adjacent(v); nl; nl = nl->tail) {
		addEdge(nl->head, u);
		decrementDegree(nl->head);
	}
	int *d = G_look(degree, u);
	printf("  After combine, degree=%d\n", *d);
	if (*d >= K && G_inNodeList(u, freezeWorklist)) {
		freezeWorklist = G_DiffNodeList(freezeWorklist, G_NodeList(u, NULL));
		spillWorklist = G_NodeList(u, spillWorklist);
	}
	printf("  - - - - - - - - - - - COMBINE END - - - - - - - - - - - -\n");
	
}

static void freeze() {
	printf("- - - - - - - - - - - FREEZE BEGIN - - - - - - - - - - -\n");

	G_node u = freezeWorklist->head;
	printf("operate on (%d,%d,%s)\n", G_nodeKey(u), Temp_int(Live_gtemp(u)), Temp_tempName(Live_gtemp(u)));

	freezeWorklist = freezeWorklist->tail;
	simplifyWorklist = G_NodeList(u, simplifyWorklist);
	freezeMoves(u);
	printf("- - - - - - - - - - - FREEZE END - - - - - - - - - - - -\n");
}

static void freezeMoves(G_node u) {
	printf("  - - - - - - - - - - - FREEZE MOVES BEGIN - - - - - - - - - - -\n");
	printf("  operate on (%d,%d,%s)\n", G_nodeKey(u), Temp_int(Live_gtemp(u)), Temp_tempName(Live_gtemp(u)));

	for (Live_moveList moves = nodeMoves(u); moves; moves = moves->tail) {
		G_node x = moves->src;
		G_node y = moves->dst;
		G_node v;
		if (nodeEqual(y, u)) {
			v = getAlias(x);
		} else {
			v = getAlias(y);
		}

		printf("  v: (%d,%d,%s)\n", G_nodeKey(v), Temp_int(Live_gtemp(v)), Temp_tempName(Live_gtemp(v)));

		activeMoves = Live_DiffMoveList(activeMoves, Live_MoveList(x, y, NULL));
		frozenMoves = Live_MoveList(x, y, frozenMoves);
		int *d = G_look(degree, v);
		printf("  v's degree: %d\n", *d);
		if (!moveRelated(v) && !inColor(v) && *d < K) {
			printf("  move v from freezeWorklist to simplifyWorklist\n");
			freezeWorklist = G_DiffNodeList(freezeWorklist, G_NodeList(v, NULL));
			simplifyWorklist = G_NodeList(v, simplifyWorklist);
		}
	}
	printf("  - - - - - - - - - - - FREEZE MOVES END - - - - - - - - - - - -\n");
}

static void selectSpill() {
	printf("  - - - - - - - - - - - SPILL BEGIN - - - - - - - - - - -\n");

	G_node m = NULL;
	int maxd = -1;
	for (G_nodeList nl = spillWorklist; nl; nl = nl->tail) {
		int *d = G_look(degree, nl->head);
		if (*d > maxd) {   // TODO: should be >
			maxd = *d;
			m = nl->head;
		}
	}
	assert(m != NULL);
	
	printf("choose to spill (%d,%d,%s)\n", G_nodeKey(m), Temp_int(Live_gtemp(m)), Temp_tempName(Live_gtemp(m)));
	spillWorklist = G_DiffNodeList(spillWorklist, G_NodeList(m, NULL));
	simplifyWorklist = G_NodeList(m, simplifyWorklist);
	freezeMoves(m);
	printf("  - - - - - - - - - - - SPILL END - - - - - - - - - - - -\n");
}

static void assignColors() {
	printf("  - - - - - - - - - - - ASSIGN COLORS BEGIN - - - - - - - - - - -\n");

	while (selectStack != NULL) {
		G_node n = selectStack->head;
		selectStack = selectStack->tail;
		if (Temp_inTempList(Live_gtemp(n), F_hardRegs())) {
			continue;
		}
		bool okColors[K];
		for (int i = 0; i < K; i++) okColors[i] = TRUE;

		G_nodeList adjList = G_succ(n);
		for (G_nodeList nl = G_nodes(graph); nl; nl = nl->tail) {
			if (nl->head != n && getAlias(nl->head) == n) {
				adjList = G_UnionNodeList(adjList, G_succ(nl->head));
			}
		}

		for (; adjList; adjList = adjList->tail) {
			G_node anode = getAlias(adjList->head);
			int *c = NULL;
			if (inColor(anode)) {
				c = G_look(color, anode);
			}/* else if (G_inNodeList(anode, coloredNodes)) {
				c = G_look(coloredNodes, anode);
			}*/ else {
				continue;
			}
			assert(c != NULL);
			assert(*c >= 0 && *c < K);
			okColors[*c] = FALSE;
		}

		int selectedColor = 0;
		for (; selectedColor < K; selectedColor++) {
			if (okColors[selectedColor]) {
				coloredNodes = G_NodeList(n, coloredNodes);
				int *c = checked_malloc(sizeof(int));
				*c = selectedColor;
				G_enter(color, n, c);
				printf("assign (%d,%d,%s) with %s\n", G_nodeKey(n), Temp_int(Live_gtemp(n)), Temp_tempName(Live_gtemp(n)), reg_name[selectedColor]);
				break;
			}
		}
		if (selectedColor == K) {
			printf("assign (%d,%d,%s) failed! SPILL!!\n", G_nodeKey(n), Temp_int(Live_gtemp(n)), Temp_tempName(Live_gtemp(n)));
			spilledNodes = G_NodeList(n, spilledNodes);
		}
	}
	if (spilledNodes == NULL) {
		for (G_nodeList nl = coalescedNodes; nl; nl = nl->tail) {
			int *c = checked_malloc(sizeof(int));
			G_node temp = getAlias(nl->head);
			int *tc = G_look(color, temp);
			*c = *tc;
			G_enter(color, nl->head, c);
		}
	}

	printf("  - - - - - - - - - - - ASSIGN COLORS END - - - - - - - - - - -\n");

}

static Temp_tempList getSpills() {
	Temp_tempList tl = NULL;
	for (G_nodeList nl = spilledNodes; nl; nl = nl->tail) {
		tl = Temp_TempList(Live_gtemp(nl->head), tl);
	}
	return tl;
}

static Temp_map getColoring() {
	if (spilledNodes) {
		return NULL;
	}
	Temp_map tm = Temp_empty();
	for (G_nodeList nl = G_nodes(graph); nl; nl = nl->tail) {
		int *c = G_look(color, nl->head);
		Temp_enter(tm, Live_gtemp(nl->head), reg_name[*c]);
	}
	// Temp_enter(tm, F_RBP(), "%rbp");
	Temp_enter(tm, F_RSP(), "%rsp");
	Temp_enter(tm, F_FKE(), "%fke");
	return tm;
}

void G_showAdj(G_nodeList nl) {
	for (; nl; nl = nl->tail) {
		G_node u = nl->head;
		printf("(%d,%d,%s) %d total: ", G_nodeKey(u), Temp_int(Live_gtemp(u)), Temp_tempName(Live_gtemp(u)), G_nllen(adjacent(u)));
		for (G_nodeList nnl = adjacent(u); nnl; nnl = nnl->tail) {
			G_node v = nnl->head;
			printf("(%d,%d,%s)", G_nodeKey(v), Temp_int(Live_gtemp(v)), Temp_tempName(Live_gtemp(v)));
		}
		printf("\n");
	}
}

struct COL_result COL_color(struct Live_graph lg, Temp_map initial, Temp_tempList regs) {
	build(lg, initial, regs);
	makeWorklist();
	while (simplifyWorklist || worklistMoves || freezeWorklist || spillWorklist) {
		printf("****************************************************\n");
		printf("****************************************************\n");
		printf("simplifyWorklist: %d\n", G_nllen(simplifyWorklist));
		// G_show(stdout, simplifyWorklist, NULL);
		G_showAdj(simplifyWorklist);
		printf("worklistMoves: %d\n", Live_mllen(worklistMoves));
		Live_showMoveList(worklistMoves);
		printf("activeMoves: %d\n", Live_mllen(activeMoves));
		Live_showMoveList(activeMoves);
		printf("freezeWorklist: %d\n", G_nllen(freezeWorklist));
		// G_show(stdout, freezeWorklist, NULL);
		G_showAdj(freezeWorklist);
		printf("spillWorklist: %d\n", G_nllen(spillWorklist));
		// G_show(stdout, spillWorklist, NULL);
		G_showAdj(spillWorklist);
		printf("spilledNodes: %d\n", G_nllen(spilledNodes));
		// G_show(stdout, spilledNodes, NULL);
		G_showAdj(spilledNodes);
		printf("frozenMoves: %d\n", Live_mllen(frozenMoves));
		Live_showMoveList(frozenMoves);
		// printf("adjSet:\n");
		// showAdjSet();
		fflush(stdout);

		if (simplifyWorklist) {
			simplify();
		} else if (worklistMoves) {
			coalesce();
		} else if (freezeWorklist) {
			freeze();
		} else if (spillWorklist) {
			selectSpill();
		}
	}
	assignColors();

	struct COL_result ret;
	ret.spills = getSpills();
	ret.coloring = getColoring();
	return ret;
}
