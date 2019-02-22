#ifndef LIVENESS_H
#define LIVENESS_H

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

struct Live_graph {
	G_graph graph;
	Live_moveList moves;
};
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

Temp_tempList List_Union(Temp_tempList a, Temp_tempList b);
Temp_tempList List_Diff(Temp_tempList a, Temp_tempList b);
bool List_inList(Temp_temp item, Temp_tempList list);
bool inMoveList(G_node src, G_node dst, Live_moveList ml);
bool List_Equal(Temp_tempList a, Temp_tempList b);

void Live_showMoveList(Live_moveList ml);
int Live_mllen(Live_moveList ml);

#endif
