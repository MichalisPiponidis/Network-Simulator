
#include <iostream>
#include <fstream>
#include <limits.h> 

#define BAUD_RATE 10.7

typedef struct {
	int* slots;
}line;

typedef struct {
	int level;
	int** callsum;
	int*** calls;
	int*** slots;
	int*** firstnode;
	int*** secondnode;
}security;

typedef struct {
	int* path_nodes;
	int* path_links;
	int hops;
	int mod_format;
	int exists;
	int weight;
}path_info;

typedef struct {
	int req_id;
	int src;
	int dst;
	int req;
	int req_slots_weight; //1
	int req_slots_weight_dis; //2
	int req_slots_weight_dis_links; //3
	int req_slots_hops; //4
	int req_slots_hops_dis; //5
	int req_slots_hops_dis_links; //6
	int startingslot;
	int type; //1=weight, ...
}call;

typedef struct {
	int num_of_calls;
	int slotssum;
	float blocking_prob;
	int calls_success;
}allocation_info;

static int nodes, i, j, k, q, w, u, slotsize, bandwidth, spacing, e, r, call_amount, allocations_amount, step, callid, taken, startingslot, callamt, choice = 0, src, dst, t, y, hop, startingslot1, taken1;
static int skip, sum, srcslot, dstslot, first, second, securitycallid, highestsecurity, currentsecurity,path;
static security xors;
static int** graph;
static int** graphtemp;
static line** contents;
static path_info** paths_weight;
static path_info** paths_weight_dis;
static path_info** paths_weight_dis_links;
static path_info** paths_hops;
static path_info** paths_hops_dis;
static path_info** paths_hops_dis_links;
static int** link_id;
static call* calls;
static allocation_info* allocations;
static FILE* fp;
static char filename[164];

void export_slot_contents();
int find_security_hops(int seccallid,int mode);
int find_security_hops_dis(int seccallid, int mode);
int find_security_weight(int seccallid, int mode);
int find_security_weight_dis(int seccallid, int mode);

int minDistance(int dist[], bool sptSet[]) {
	int min = INT_MAX, min_index=0;
	for (int v = 0; v < nodes; v++)
		if (sptSet[v] == false && dist[v] <= min)
			min = dist[v], min_index = v;
	return min_index;
}

void print_path_hops_dis(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_hops_dis[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_hops_dis(parent, parent[dst], src, dest);
	e++;
	paths_hops_dis[src][dest].path_nodes[e] = dst;
	paths_hops_dis[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_hops_dis[src][dest].weight = paths_hops_dis[src][dest].weight + graphtemp[parent[dst]][dst];
	r++;
}

void print_path_hops(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_hops[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_hops(parent, parent[dst], src, dest);
	e++;
	paths_hops[src][dest].path_nodes[e] = dst;
	paths_hops[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_hops[src][dest].weight = paths_hops[src][dest].weight + graph[parent[dst]][dst];
	r++;
}

void print_path_weight_dis(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_weight_dis[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_weight_dis(parent, parent[dst], src, dest);
	e++;
	paths_weight_dis[src][dest].path_nodes[e] = dst;
	paths_weight_dis[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_weight_dis[src][dest].weight = paths_weight_dis[src][dest].weight + graphtemp[parent[dst]][dst];
	r++;
}

void print_path_weight_dis_links(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_weight_dis_links[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_weight_dis_links(parent, parent[dst], src, dest);
	e++;
	paths_weight_dis_links[src][dest].path_nodes[e] = dst;
	paths_weight_dis_links[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_weight_dis_links[src][dest].weight = paths_weight_dis_links[src][dest].weight + graphtemp[parent[dst]][dst];
	r++;
}

void print_path_hops_dis_links(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_hops_dis_links[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_hops_dis_links(parent, parent[dst], src, dest);
	e++;
	paths_hops_dis_links[src][dest].path_nodes[e] = dst;
	paths_hops_dis_links[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_hops_dis_links[src][dest].weight = paths_hops_dis_links[src][dest].weight + graphtemp[parent[dst]][dst];
	r++;
}

void print_path_weight(const int* parent, int dst, int src, int dest) {
	if (parent[dst] == -1) {
		paths_weight[src][dest].path_nodes[e] = dst;
		return;
	}
	print_path_weight(parent, parent[dst], src, dest);
	e++;
	paths_weight[src][dest].path_nodes[e] = dst;
	paths_weight[src][dest].path_links[r] = link_id[parent[dst]][dst];
	paths_weight[src][dest].weight = paths_weight[src][dest].weight + graph[parent[dst]][dst];
	r++;
}

void dijkstra_hops(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_hops[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	for (int count = 0; count < V ; count++) {
		int u = minDistance(dist, sptSet);
		if (dist[u] == INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graph[u][v] && dist[u] != INT_MAX && dist[u] + graph[u][v] < dist[v]) {
					dist[v] = dist[u] + graph[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graph[u][v] && dist[v] > dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
				}
			}
		}
	}
	e = 0;
	r = 0;
	print_path_hops(parent, dst, src, dst);
	paths_hops[src][dst].hops = e;
}

void dijkstra_hops_dis(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_hops_dis[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	paths_hops_dis[src][dst].exists = 0;
	for (int count = 0; count < V ; count++) {
		int u = minDistance(dist, sptSet);
		if (dist[u]==INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graphtemp[u][v] && dist[u] != INT_MAX && dist[u] + graphtemp[u][v] < dist[v]) {
					dist[v] = dist[u] + graphtemp[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graphtemp[u][v] && dist[v] > dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
					/*if (src == 0 && dst == 4) {
						printf("\nparent[%d]=%d\t", v, u);
						system("pause");
					}*/
					
				}
			}
		}
		// printf("src: %d dst: %d u= %d ,count = %d\n",src,dst, u,count);
		if (u == dst) {
			paths_hops_dis[src][dst].exists = 1;
		}
	}
	e = 0;
	r = 0;
	parent[src] = -1;
	if (paths_hops_dis[src][dst].exists == 1) {
		print_path_hops_dis(parent, dst, src, dst);
		paths_hops_dis[src][dst].hops = e;
	}
}

void dijkstra_weight_dis(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_weight_dis[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	paths_weight_dis[src][dst].exists = 0;
	for (int count = 0; count < V ; count++) {
		int u = minDistance(dist, sptSet);
		if (dist[u] == INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graphtemp[u][v] && dist[u] != INT_MAX && dist[u] + graphtemp[u][v] < dist[v]) {
					dist[v] = dist[u] + graphtemp[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graphtemp[u][v] && dist[v] > dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
				}
			}
		}
		if (u == dst)
			paths_weight_dis[src][dst].exists = 1;
	}
	e = 0;
	r = 0;
	if (paths_weight_dis[src][dst].exists == 1) {
		print_path_weight_dis(parent, dst, src, dst);
		paths_weight_dis[src][dst].hops = e;
	}
}

void dijkstra_weight_dis_links(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_weight_dis_links[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	paths_weight_dis_links[src][dst].exists = 0;
	for (int count = 0; count < V; count++) {
		int u = minDistance(dist, sptSet);
		if (dist[u] == INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graphtemp[u][v] && dist[u] != INT_MAX && dist[u] + graphtemp[u][v] < dist[v]) {
					dist[v] = dist[u] + graphtemp[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graphtemp[u][v] && dist[v] > dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
				}
			}
		}
		if (u == dst)
			paths_weight_dis_links[src][dst].exists = 1;
	}
	e = 0;
	r = 0;
	if (paths_weight_dis_links[src][dst].exists == 1) {
		print_path_weight_dis_links(parent, dst, src, dst);
		paths_weight_dis_links[src][dst].hops = e;
	}
}

void dijkstra_hops_dis_links(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_hops_dis_links[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	paths_hops_dis_links[src][dst].exists = 0;
	for (int count = 0; count < V ; count++) {
		int u = minDistance(dist, sptSet);
		if (dist[u] == INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graphtemp[u][v] && dist[u] != INT_MAX && dist[u] + graphtemp[u][v] < dist[v]) {
					dist[v] = dist[u] + graphtemp[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graphtemp[u][v] && dist[v] > dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
				}
			}
		}
		if (u == dst)
			paths_hops_dis_links[src][dst].exists = 1;
	}
	e = 0;
	r = 0;
	if (paths_hops_dis_links[src][dst].exists == 1) {
		print_path_hops_dis_links(parent, dst, src, dst);
		paths_hops_dis_links[src][dst].hops = e;
	}
}

void dijkstra_weight(int src, int dst, int mode) { //mode: 0 for shortest weight, 1 for shortest hops
	int V = nodes;
	int w = 0;
	int* dist;
	int* parent;
	bool* sptSet;
	dist = new int[nodes];
	parent = new int[nodes] {};
	sptSet = new bool[nodes];
	paths_weight[src][dst].weight = 0;
	parent[src] = -1;
	for (i = 0; i < V; i++) {
		dist[i] = INT_MAX;
		sptSet[i] = false;
	}
	dist[src] = 0;
	for (int count = 0; count < V ; count++){ 
		int u = minDistance(dist, sptSet);
		if (dist[u] == INT_MAX) {
			break;
		}
		sptSet[u] = true;
		for (int v = 0; v < V; v++) {
			if (mode == 0) {
				if (!sptSet[v] && graph[u][v] && dist[u] != INT_MAX && dist[u] + graph[u][v] < dist[v]) {
					dist[v] = dist[u] + graph[u][v];
					parent[v] = u;
				}
			}
			else {
				if (!sptSet[v] && graph[u][v] && dist[v]>dist[u]) {
					if (dist[u] == INT_MAX) {
						dist[v] = 1;
					}
					else {
						dist[v] = dist[u] + 1;
					}
					parent[v] = u;
				}
			}
		}
	}
	e = 0;
	r = 0;
	print_path_weight(parent, dst, src, dst);
	paths_weight[src][dst].hops = e;
}

void make_slots() {
	fopen_s(&fp, "parameters.txt", "r");
	fscanf_s(fp, "%d", &bandwidth);
	fscanf_s(fp, "%d", &spacing);
	slotsize = bandwidth / spacing;
	contents = new line* [nodes];
	for (i = 0; i < nodes; i++) {
		contents[i] = new line[nodes] {};
		for (j = 0; j < nodes; j++) {
			contents[i][j].slots = new int[slotsize] {};
		}
	}
	fclose(fp);
}

void make_link_id() {
	link_id = new int* [nodes];
	for (i = 0; i < nodes; i++) {
		link_id[i] = new int[nodes] {};
	}
	k = 1;
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			if (graph[i][j] != 0) {
				link_id[i][j] = k;
				k++;
			}
		}
	}
}

void print_link_id() {
	i = 0;
	j = 0;
	printf("\nLink ID:\n\n");
	while (i < nodes) {
		printf("%d ", link_id[i][j]);
		j++;
		if (j >= nodes) {
			j = 0;
			i++;
			printf("\n");
		}
	}
}

void read_graph() {
	j = 0;
	graph = new int* [nodes];
	for (i = 0; i < nodes; i++) {
		graph[i] = new int[nodes] {};
	}
	i = 0;
	while (i < nodes){
		fscanf_s(fp, "%d", &graph[i][j]);
		j++;
		if (j >= nodes){
			j = 0;
			i++;
		}
	}
	fclose(fp);
}

void print_graph() {
	i = 0;
	j = 0;
	printf("\nGraph:\n\n");
	while (i < nodes){
		printf ("%d ",graph[i][j]);
		j++;
		if (j >= nodes){
			j = 0;
			i++;
			printf("\n");
		}
	}
	printf("\n");
}

void find_mod_format_hops_dis(int src, int dst, int distance) {
	if (distance > 4600)
		paths_hops_dis[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_hops_dis[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_hops_dis[src][dst].mod_format = 3;
	else
		paths_hops_dis[src][dst].mod_format = 4;
}

void find_mod_format_hops_dis_links(int src, int dst, int distance) {
	if (distance > 4600)
		paths_hops_dis_links[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_hops_dis_links[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_hops_dis_links[src][dst].mod_format = 3;
	else
		paths_hops_dis_links[src][dst].mod_format = 4;
}

void find_mod_format_hops(int src, int dst, int distance) {
	if (distance > 4600)
		paths_hops[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_hops[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_hops[src][dst].mod_format = 3;
	else
		paths_hops[src][dst].mod_format = 4;
}

void find_mod_format_weight_dis(int src, int dst, int distance) {
	if (distance > 4600)
		paths_weight_dis[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_weight_dis[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_weight_dis[src][dst].mod_format = 3;
	else
		paths_weight_dis[src][dst].mod_format = 4;
}

void find_mod_format_weight_dis_links(int src, int dst, int distance) {
	if (distance > 4600)
		paths_weight_dis_links[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_weight_dis_links[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_weight_dis_links[src][dst].mod_format = 3;
	else
		paths_weight_dis_links[src][dst].mod_format = 4;
}

void find_mod_format_weight(int src, int dst, int distance) {
	if (distance > 4600)
		paths_weight[src][dst].mod_format = 1;
	else if (distance > 1700)
		paths_weight[src][dst].mod_format = 2;
	else if (distance > 800)
		paths_weight[src][dst].mod_format = 3;
	else
		paths_weight[src][dst].mod_format = 4;
}

int slots_for_call(int req, int mod) {
	return (int)ceil(((req) / (BAUD_RATE * mod)));
}

void allocations_weight_hops_disjoint() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try weight
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops
				i = 0;
				while (startingslot == -1) { //starting slot
					taken = 0;
					for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1)
							continue;
					}
					if (taken == 0) {
						startingslot = i;
					}
					i++;
					if (i > slotsize) {
						break;
					}
				}
				if (startingslot == -1) { //hops not available, try weight disjoint
					if (paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) {
						i = 0;
						while (startingslot == -1) { //starting slot
							taken = 0;
							for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
								for (j = 0; j < calls[callid - 1].req_slots_weight_dis; j++) { //req slots
									if ((i + j) < slotsize) {
										if ((contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
											taken = 1;
											continue;
										}
									}
									else {
										taken = 1;
										continue;
									}
								}
								if (taken == 1)
									continue;
							}
							if (taken == 0) {
								startingslot = i;
							}
							i++;
							if (i > slotsize) {
								break;
							}
						}
					}
					if (startingslot == -1) { //weight disjoint not available, try hops disjoint
						if (paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) {
							i = 0;
							while (startingslot == -1) { //starting slot
								taken = 0;
								for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
									for (j = 0; j < calls[callid - 1].req_slots_hops_dis; j++) { //req slots
										if ((i + j) < slotsize) {
											if ((contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
												taken = 1;
												continue;
											}
										}
										else {
											taken = 1;
											continue;
										}
									}
									if (taken == 1)
										continue;
								}
								if (taken == 0) {
									startingslot = i;
								}
								i++;
								if (i > slotsize) {
									break;
								}
							}
						}
						if (startingslot == -1) { //nothing available
						}
						else {
							calls[callid - 1].startingslot = startingslot;
							calls[callid - 1].type = 5;
							allocations[allocations_amount].calls_success++;
							for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
								for (j = startingslot; j < calls[callid - 1].req_slots_hops_dis + startingslot; j++) {
									contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
									allocations[allocations_amount].slotssum++;
								}
							}
						}
					}
					else {
						calls[callid - 1].startingslot = startingslot;
						calls[callid - 1].type = 2;
						allocations[allocations_amount].calls_success++;
						for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
							for (j = startingslot; j < calls[callid - 1].req_slots_weight_dis + startingslot; j++) {
								contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
								allocations[allocations_amount].slotssum++;
							}
						}
					}
				}
				else {
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 4;
					allocations[allocations_amount].calls_success++;
					for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
						for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
							contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 1;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
						contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_weight_hops() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try weight
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops
				i = 0;
				while (startingslot == -1) { //starting slot
					taken = 0;
					for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1)
							continue;
					}
					if (taken == 0) {
						startingslot = i;
					}
					i++;
					if (i > slotsize) {
						break;
					}
				}
				if (startingslot == -1) { //hops not available, try weight disjoint
					
				}
				else {
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 4;
					allocations[allocations_amount].calls_success++;
					for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
						for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
							contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 1;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
						contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_weight() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try weight
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops
				
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 1;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
						contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_bestfit() {
	int i2, j2, k2,j3, mode, secured=0;
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			calls[callid - 1].startingslot = -1;
			highestsecurity = -1;
			i2 = 0;
			mode = 0;
			printf("\ncallid=%d", callid);
			//Weight
			while (i2 < slotsize) {
				taken = 0; //try weight
					for (k2 = 0; k2 < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) { //link
						for (j3 = 0; j3 < calls[callid - 1].req_slots_weight; j3++) { //req slots
							if ((i2 + j3) < slotsize) {
								if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[i2 + j3]) != 0) {
									taken = 1;
									break;
								}
							}
							else {
								taken = 1;
								break;
							}
						}
						if (taken == 1)
							break;
					}
					if (taken == 0) {
						calls[callid - 1].startingslot = i2;
						calls[callid - 1].type = 1;
						//printf("\nStarting Slot=%d", calls[callid - 1].startingslot);
						currentsecurity = find_security_weight(callid,0);
						if (currentsecurity > highestsecurity) {
							startingslot = i2;
							highestsecurity = currentsecurity;
							mode = 1;
						}
					}
					i2++;
			}
			//Hops
			i2 = 0;
			while (i2 < slotsize) {
					taken = 0; //try hops
					for (k2 = 0; k2 < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) { //link
						for (j3 = 0; j3 < calls[callid - 1].req_slots_hops; j3++) { //req slots
							if ((i2 + j3) < slotsize) {
								if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[i2 + j3]) != 0) {
									taken = 1;
									break;
								}
							}
							else {
								taken = 1;
								break;
							}
						}
						if (taken == 1)
							break;
					}
					if (taken == 0) {
						calls[callid - 1].startingslot = i2;
						calls[callid - 1].type = 4;
						currentsecurity = find_security_hops(callid,0);
						if (currentsecurity >= highestsecurity) {
							startingslot = i2;
							highestsecurity = currentsecurity;
							mode = 2;
						}
					}
					i2++;
			}
			//Hops disjoint
			i2 = 0;
			while (i2 < slotsize) {
					taken = 0; //try hops dis
					for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_hops_dis; j++) { //req slots
							if ((i2 + j) < slotsize) {
								if ((contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i2 + j]) != 0) {
									taken = 1;
									break;
								}
							}
							else {
								taken = 1;
								break;
							}
						}
						if (taken == 1)
							break;
					}
					if (taken == 0) {
						calls[callid - 1].startingslot = i2;
						calls[callid - 1].type = 5;
						currentsecurity = find_security_hops_dis(callid,0);
						if (currentsecurity > highestsecurity) {
							startingslot = i2;
							highestsecurity = currentsecurity;
							mode = 3;
						}
					}
					i2++;
			}
			//Weight disjoint
			i2 = 0;
			while (i2 < slotsize) {
					taken = 0; //try weight disjoint
					for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_weight_dis; j++) { //req slots
							if ((i2 + j) < slotsize) {
								if ((contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i2 + j]) != 0) {
									taken = 1;
									break;
								}
							}
							else {
								taken = 1;
								break;
							}
						}
						if (taken == 1)
							break;
					}
					if (taken == 0) {
						calls[callid - 1].startingslot = i2;
						calls[callid - 1].type = 2;
						currentsecurity = find_security_weight_dis(callid,0);
						if (currentsecurity > highestsecurity) {
							startingslot = i2;
							highestsecurity = currentsecurity;
							mode = 4;
						}
					}
					i2++;
			}
			if (startingslot == -1) { //nothing available
				printf("\tFAIL");
			}
			else {
				if (highestsecurity > 0)
					secured++;
				//printf("\nCall:%d Highest security=%d starting slot=%d\t",callid, highestsecurity, calls[callid-1].startingslot); // tempp
				if (mode == 1) { //Weight has the highest security.
					printf("\tSUCCESS\tstartingslot: %d\tmode: Weight\t\tsecurity: %d\treq slots: %d", startingslot, highestsecurity, calls[callid - 1].req_slots_weight);
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 1;
					allocations[allocations_amount].calls_success++;
					for (k2 = 0; k2 < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) {
						for (j2 = startingslot; j2 < calls[callid - 1].req_slots_weight + startingslot; j2++) {
							contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[j2] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
				if (mode == 2) { //Hops has the highest security.
					printf("\tSUCCESS\tstartingslot: %d\tmode: Hops\t\tsecurity: %d\treq slots: %d", startingslot, highestsecurity, calls[callid - 1].req_slots_hops);
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 4;
					allocations[allocations_amount].calls_success++;
					for (k2 = 0; k2 < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) {
						for (j2 = startingslot; j2 < calls[callid - 1].req_slots_hops + startingslot; j2++) {
							contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[j2] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
				if (mode == 3) { //Hops Disjoint has the highest security.
					printf("\tSUCCESS\tstartingslot: %d\tmode: Hops Dis\t\tsecurity: %d\treq slots: %d", startingslot, highestsecurity, calls[callid - 1].req_slots_hops_dis);
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 5;
					allocations[allocations_amount].calls_success++;
					for (k2 = 0; k2 < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) {
						for (j2 = startingslot; j2 < calls[callid - 1].req_slots_hops_dis + startingslot; j2++) {
							contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[j2] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
				if (mode == 4) { //Weight Disjoint has the highest security.
					printf("\tSUCCESS\tstartingslot: %d\tmode: Weight Dis\tsecurity: %d\treq slots: %d", startingslot, highestsecurity, calls[callid - 1].req_slots_weight_dis);
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 2;
					allocations[allocations_amount].calls_success++;
					for (k2 = 0; k2 < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k2++) {
						for (j2 = startingslot; j2 < calls[callid - 1].req_slots_weight_dis + startingslot; j2++) {
							contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k2 + 1]].slots[j2] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
				//if (callid > 1500) { // tempp
				//	export_slot_contents();
				//	system("pause");
				//}
			}
		}
		printf("\n\n%d Calls secured of %d.", secured, callamt);
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
		printf("\nSlots used: %d", allocations[allocations_amount - 1].slotssum);
		printf("\nCalls Inserted: %d of %d. Blocking Probability: %f", allocations[allocations_amount-1].calls_success, callamt, allocations[allocations_amount-1].blocking_prob);
	}
}

void allocations_weight_protected() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try weight
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				if ((paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) && (taken == 0)) {
					for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_weight_dis; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1) {
							continue;
						}
					}
				}
				else {
					taken = 1;
				}
				if (taken == 1) {
					startingslot = -1;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops

			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 1;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
						contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
				for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight_dis + startingslot; j++) {
						contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_weight_protected_links() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try weight
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				if ((paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) && (taken == 0)) {
					for (k = 0; k < paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_weight_dis_links; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1) {
							continue;
						}
					}
				}
				else {
					taken = 1;
				}
				if (taken == 1) {
					startingslot = -1;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops

			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 1;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
						contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
				for (k = 0; k < paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_weight_dis_links + startingslot; j++) {
						contents[paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_hops_protected() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try hops
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				if ((paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) && (taken == 0)) {
					for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_hops_dis; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1) {
							continue;
						}
					}
				}
				else {
					taken = 1;
				}
				if (taken == 1) {
					startingslot = -1;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //weight not available, try hops
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 4;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
						contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
				for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops_dis + startingslot; j++) {
						contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_hops_protected_links() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try hops
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				if ((paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) && (taken == 0)) {
					for (k = 0; k < paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_hops_dis_links; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1) {
							continue;
						}
					}
				}
				else {
					taken = 1;
				}
				if (taken == 1) {
					startingslot = -1;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { 
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 4;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
						contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
				for (k = 0; k < paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops_dis_links + startingslot; j++) {
						contents[paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis_links[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_hops_weight_disjoint() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try hops
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //hops not available, try weight
				i = 0;
				while (startingslot == -1) { //starting slot
					taken = 0;
					for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1)
							continue;
					}
					if (taken == 0) {
						startingslot = i;
					}
					i++;
					if (i > slotsize) {
						break;
					}
				}
				if (startingslot == -1) { //weight not available, try weight disjoint
					if (paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) {
						i = 0;
						while (startingslot == -1) { //starting slot
							taken = 0;
							for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
								for (j = 0; j < calls[callid - 1].req_slots_weight_dis; j++) { //req slots
									if ((i + j) < slotsize) {
										if ((contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
											taken = 1;
											continue;
										}
									}
									else {
										taken = 1;
										continue;
									}
								}
								if (taken == 1)
									continue;
							}
							if (taken == 0) {
								startingslot = i;
							}
							i++;
							if (i > slotsize) {
								break;
							}
						}
					}
					if (startingslot == -1) { //weight disjoint not available, try hops disjoint
						if (paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].exists == 1) {
							i = 0;
							while (startingslot == -1) { //starting slot
								taken = 0;
								for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
									for (j = 0; j < calls[callid - 1].req_slots_hops_dis; j++) { //req slots
										if ((i + j) < slotsize) {
											if ((contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
												taken = 1;
												continue;
											}
										}
										else {
											taken = 1;
											continue;
										}
									}
									if (taken == 1)
										continue;
								}
								if (taken == 0) {
									startingslot = i;
								}
								i++;
								if (i > slotsize) {
									break;
								}
							}
						}
						if (startingslot == -1) { //nothing available
						}
						else {
							calls[callid - 1].startingslot = startingslot;
							calls[callid - 1].type = 5;
							allocations[allocations_amount].calls_success++;
							for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
								for (j = startingslot; j < calls[callid - 1].req_slots_hops_dis + startingslot; j++) {
									contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
									allocations[allocations_amount].slotssum++;
								}
							}
						}
					}
					else {
						calls[callid - 1].startingslot = startingslot;
						calls[callid - 1].type = 2;
						allocations[allocations_amount].calls_success++;
						for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
							for (j = startingslot; j < calls[callid - 1].req_slots_weight_dis + startingslot; j++) {
								contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
								allocations[allocations_amount].slotssum++;
							}
						}
					}
				}
				else {
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 1;
					allocations[allocations_amount].calls_success++;
					for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
						for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
							contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
			}
			else {
			calls[callid - 1].startingslot = startingslot;
			calls[callid - 1].type = 4;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
						contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_hops_weight() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try hops
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //hops not available, try weight
				i = 0;
				while (startingslot == -1) { //starting slot
					taken = 0;
					for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
						for (j = 0; j < calls[callid - 1].req_slots_weight; j++) { //req slots
							if ((i + j) < slotsize) {
								if ((contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
									taken = 1;
									continue;
								}
							}
							else {
								taken = 1;
								continue;
							}
						}
						if (taken == 1)
							continue;
					}
					if (taken == 0) {
						startingslot = i;
					}
					i++;
					if (i > slotsize) {
						break;
					}
				}
				if (startingslot == -1) { //weight not available, try weight disjoint
					
				}
				else {
					calls[callid - 1].startingslot = startingslot;
					calls[callid - 1].type = 1;
					allocations[allocations_amount].calls_success++;
					for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
						for (j = startingslot; j < calls[callid - 1].req_slots_weight + startingslot; j++) {
							contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
							allocations[allocations_amount].slotssum++;
						}
					}
				}
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 4;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
						contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void allocations_hops() {
	allocations_amount = 0;
	for (callamt = step; callamt <= call_amount; callamt = callamt + step) {
		for (i = 0; i < nodes; i++) { //arxikopiisi content
			for (j = 0; j < nodes; j++) {
				for (k = 0; k < slotsize; k++) {
					contents[i][j].slots[k] = 0;
				}
			}
		}
		allocations[allocations_amount].num_of_calls = callamt;
		allocations[allocations_amount].calls_success = 0;
		allocations[allocations_amount].slotssum = 0;
		for (callid = 1; callid <= callamt; callid++) {
			startingslot = -1;
			i = 0;
			while (startingslot == -1) { //starting slot
				taken = 0; //try hops
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) { //link
					for (j = 0; j < calls[callid - 1].req_slots_hops; j++) { //req slots
						if ((i + j) < slotsize) {
							if ((contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[i + j]) != 0) {
								taken = 1;
								continue;
							}
						}
						else {
							taken = 1;
							continue;
						}
					}
					if (taken == 1)
						continue;
				}
				if (taken == 0) {
					startingslot = i;
				}
				i++;
				if (i > slotsize) {
					break;
				}
			}
			if (startingslot == -1) { //hops not available, try weight
				
			}
			else {
				calls[callid - 1].startingslot = startingslot;
				calls[callid - 1].type = 4;
				allocations[allocations_amount].calls_success++;
				for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
					for (j = startingslot; j < calls[callid - 1].req_slots_hops + startingslot; j++) {
						contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
						allocations[allocations_amount].slotssum++;
					}
				}
			}
		}
		allocations[allocations_amount].blocking_prob = (float)1 - ((float)allocations[allocations_amount].calls_success / (float)allocations[allocations_amount].num_of_calls);
		allocations_amount++;
	}
}

void save_weight() {
	fopen_s(&fp, "allocations_weight.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_weight_protected() {
	fopen_s(&fp, "allocations_weight_protected.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_weight_protected_links() {
	fopen_s(&fp, "allocations_weight_protected_links.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_hops_protected() {
	fopen_s(&fp, "allocations_hops_protected.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_hops_protected_links() {
	fopen_s(&fp, "allocations_hops_protected_links.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_weight_hops() {
	fopen_s(&fp, "allocations_weight_hops.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_weight_hops_disjoint() {
	fopen_s(&fp, "allocations_weight_hops_disjoint.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_hops() {
	fopen_s(&fp, "allocations_hops.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_hops_weight() {
	fopen_s(&fp, "allocations_hops_weight.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void save_hops_weight_disjoint() {
	fopen_s(&fp, "allocations_hops_weight_disjoint.txt", "w");
	fprintf_s(fp, "Allocation no.\tNum of Calls\tSuccessful Calls\tBlocking Probability\tTotal Slots used\n");
	for (i = 0; i < allocations_amount; i++) {
		fprintf_s(fp, "%d\t%d\t%d\t%f\t%d\n", i + 1, allocations[i].num_of_calls, allocations[i].calls_success, allocations[i].blocking_prob, allocations[i].slotssum);
	}
	fclose(fp);
}

void make_paths_table() {
	for (t = 0; t < nodes; t++) { //weight
		for (y = 0; y < nodes; y++) {
			if (t == y) {
				paths_weight[t][y].hops = 0;
				paths_weight[t][y].mod_format = 0;
				paths_weight[t][y].weight = 0;
			}
			else {
				dijkstra_weight(t, y, 0);
				find_mod_format_weight(t, y, paths_weight[t][y].weight);
			}
		}
	}
	for (t = 0; t < nodes; t++) { //hops
		for (y = 0; y < nodes; y++) {
			if (t == y) {
				paths_hops[t][y].hops = 0;
				paths_hops[t][y].weight = 0;
				paths_hops[t][y].mod_format = 0;
			}
			else {
				dijkstra_hops(t, y, 1);
				find_mod_format_hops(t, y, paths_hops[t][y].weight);
			}
		}
	}
	for (t = 0; t < nodes; t++) { //weight disjoint
		for (y = 0; y < nodes; y++) {
			if (t != y) {
				for (i = 0; i < nodes; i++)
					for (j = 0; j < nodes; j++)
						graphtemp[i][j] = graph[i][j];
				for (i = 0; i < paths_weight[t][y].hops; i++) {
					if ((paths_weight[t][y].path_nodes[i + 1]) != y) {
						for (j = 0; j < nodes; j++) {
							graphtemp[paths_weight[t][y].path_nodes[i + 1]][j] = 0;
							graphtemp[j][paths_weight[t][y].path_nodes[i + 1]] = 0;
						}
					}
					else {
						graphtemp[paths_weight[t][y].path_nodes[i + 1]][paths_weight[t][y].path_nodes[i]] = 0;
						graphtemp[paths_weight[t][y].path_nodes[i]][paths_weight[t][y].path_nodes[i + 1]] = 0;
					}
				}
			}
			if (t == y) {
				paths_weight_dis[t][y].hops = 0;
				paths_weight_dis[t][y].weight = 0;
				paths_weight_dis[t][y].mod_format = 0;
			}
			else {
				dijkstra_weight_dis(t, y, 0);
				find_mod_format_weight_dis(t, y, paths_weight_dis[t][y].weight);
			}
		}
	}
	for (t = 0; t < nodes; t++) { //hops disjoint
		for (y = 0; y < nodes; y++) {
			if (t != y) {
				for (i = 0; i < nodes; i++)
					for (j = 0; j < nodes; j++)
						graphtemp[i][j] = graph[i][j];
				for (i = 0; i < paths_hops[t][y].hops; i++) {
					if ((paths_hops[t][y].path_nodes[i + 1]) != y) {
						for (j = 0; j < nodes; j++) {
							graphtemp[paths_hops[t][y].path_nodes[i + 1]][j] = 0;
							graphtemp[j][paths_hops[t][y].path_nodes[i + 1]] = 0;
						}
					}
					else {
						graphtemp[paths_hops[t][y].path_nodes[i + 1]][paths_hops[t][y].path_nodes[i]] = 0;
						graphtemp[paths_hops[t][y].path_nodes[i]][paths_hops[t][y].path_nodes[i + 1]] = 0;
					}
				}
			}
			if (t == y) {
				paths_hops_dis[t][y].hops = 0;
				paths_hops_dis[t][y].weight = 0;
				paths_hops_dis[t][y].mod_format = 0;
			}
			else {
				/*for (i = 0; i < paths_hops[t][y].hops; i++)
					printf("%d - %d,", paths_hops[t][y].path_nodes[i], paths_hops[t][y].path_nodes[i + 1]);
				printf("\n");
				system("pause");
				for (i = 0; i < nodes; i++) {
					for (j = 0; j < nodes; j++)
						printf("%d\t",graphtemp[i][j]);
					printf("\n");
				}
				printf("\n");
				printf("\n");
				for (i = 0; i < nodes; i++) {
					for (j = 0; j < nodes; j++)
						printf("%d\t", (graph[i][j]-graphtemp[i][j]));
					printf("\n");
				}
				system("pause");*/

				dijkstra_hops_dis(t, y, 1);
				find_mod_format_hops_dis(t, y, paths_hops_dis[t][y].weight);
			}
		}
	}
	for (t = 0; t < nodes; t++) { //weight disjoint links
		for (y = 0; y < nodes; y++) {
			if (t != y) {
				for (i = 0; i < nodes; i++)
					for (j = 0; j < nodes; j++)
						graphtemp[i][j] = graph[i][j];
				for (i = 0; i < paths_weight[t][y].hops; i++) {
					graphtemp[paths_weight[t][y].path_nodes[i + 1]][paths_weight[t][y].path_nodes[i]] = 0;
					graphtemp[paths_weight[t][y].path_nodes[i]][paths_weight[t][y].path_nodes[i + 1]] = 0;
				}
			}
			if (t == y) {
				paths_weight_dis_links[t][y].hops = 0;
				paths_weight_dis_links[t][y].weight = 0;
				paths_weight_dis_links[t][y].mod_format = 0;
			}
			else {
				dijkstra_weight_dis_links(t, y, 0);
				find_mod_format_weight_dis_links(t, y, paths_weight_dis_links[t][y].weight);
			}
		}
	}
	for (t = 0; t < nodes; t++) { //hops disjoint links
		for (y = 0; y < nodes; y++) {
			if (t != y) {
				for (i = 0; i < nodes; i++)
					for (j = 0; j < nodes; j++)
						graphtemp[i][j] = graph[i][j];
				for (i = 0; i < paths_hops[t][y].hops; i++) {
					graphtemp[paths_hops[t][y].path_nodes[i + 1]][paths_hops[t][y].path_nodes[i]] = 0;
					graphtemp[paths_hops[t][y].path_nodes[i]][paths_hops[t][y].path_nodes[i + 1]] = 0;
				}
			}
			if (t == y) {
				paths_hops_dis_links[t][y].hops = 0;
				paths_hops_dis_links[t][y].weight = 0;
				paths_hops_dis_links[t][y].mod_format = 0;
			}
			else {
				/*for (i = 0; i < paths_hops[t][y].hops; i++)
					printf("%d - %d,", paths_hops[t][y].path_nodes[i], paths_hops[t][y].path_nodes[i + 1]);
				printf("\n");
				system("pause");
				for (i = 0; i < nodes; i++) {
					for (j = 0; j < nodes; j++)
						printf("%d\t",graphtemp[i][j]);
					printf("\n");
				}
				printf("\n");
				printf("\n");
				for (i = 0; i < nodes; i++) {
					for (j = 0; j < nodes; j++)
						printf("%d\t", (graph[i][j]-graphtemp[i][j]));
					printf("\n");
				}
				system("pause");*/

				dijkstra_hops_dis_links(t, y, 1);
				find_mod_format_hops_dis_links(t, y, paths_hops_dis_links[t][y].weight);
			}
		}
	}
}

void make_calls_table() {
	fopen_s(&fp, filename, "r");
	fscanf_s(fp, "%d", &call_amount);
	calls = new call[call_amount];
	for (i = 0; i < call_amount; i++) {
		fscanf_s(fp, "%d", &calls[i].req_id);
		fscanf_s(fp, "%d", &calls[i].src);
		fscanf_s(fp, "%d", &calls[i].dst);
		fscanf_s(fp, "%d", &calls[i].req);
		calls[i].src = calls[i].src - 1;
		calls[i].dst = calls[i].dst - 1;
		calls[i].req_slots_weight = slots_for_call(calls[i].req, paths_weight[calls[i].src][calls[i].dst].mod_format);
		calls[i].req_slots_hops = slots_for_call(calls[i].req, paths_hops[calls[i].src][calls[i].dst].mod_format);
		calls[i].req_slots_weight_dis = slots_for_call(calls[i].req, paths_weight_dis[calls[i].src][calls[i].dst].mod_format);
		calls[i].req_slots_weight_dis_links = slots_for_call(calls[i].req, paths_weight_dis_links[calls[i].src][calls[i].dst].mod_format);
		calls[i].req_slots_hops_dis = slots_for_call(calls[i].req, paths_hops_dis[calls[i].src][calls[i].dst].mod_format);
		calls[i].req_slots_hops_dis_links = slots_for_call(calls[i].req, paths_hops_dis_links[calls[i].src][calls[i].dst].mod_format);
	}
	fclose(fp);
}

void export_paths_hops() {
	fopen_s(&fp, "paths_hops.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
				fprintf_s(fp, "%d\t%d\t%d",i,j, paths_hops[i][j].hops + 1);
				for (k = 0; k < paths_hops[i][j].hops + 1; k++) {
					fprintf_s(fp, "\t%d", paths_hops[i][j].path_nodes[k]);
				}
				if (i == 0 && j == 0) {
					fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
				}
				fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void export_paths_weight() {
	fopen_s(&fp, "paths_weight.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d\t%d\t%d", i, j, paths_weight[i][j].hops + 1);
			for (k = 0; k < paths_weight[i][j].hops + 1; k++) {
				fprintf_s(fp, "\t%d", paths_weight[i][j].path_nodes[k]);
			}
			if (i == 0 && j == 0) {
				fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void export_paths_used() { //export which path each call uses
	fopen_s(&fp, "paths_used.txt", "w");
	for (i = 0; i < call_amount; i++) {
			fprintf_s(fp, "%d", calls[i].type);
			fprintf_s(fp, "\n");
	}
	fclose(fp);
}

void import_paths_used() { //export which path each call uses
	fopen_s(&fp, "paths_used.txt", "r");
	for (i = 0; i < call_amount; i++) {
		fscanf_s(fp, "%d", &calls[i].type);
	}
	fclose(fp);
}

void export_paths_hops_dis() {
	fopen_s(&fp, "paths_hops_dis.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d\t%d\t%d", i, j, paths_hops_dis[i][j].hops + 1);
			for (k = 0; k < paths_hops_dis[i][j].hops + 1; k++) {
				fprintf_s(fp, "\t%d", paths_hops_dis[i][j].path_nodes[k]);
			}
			if (i == 0 && j == 0) {
				fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void export_paths_hops_dis_links() {
	fopen_s(&fp, "paths_hops_dis_links.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d\t%d\t%d", i, j, paths_hops_dis_links[i][j].hops + 1);
			for (k = 0; k < paths_hops_dis_links[i][j].hops + 1; k++) {
				fprintf_s(fp, "\t%d", paths_hops_dis_links[i][j].path_nodes[k]);
			}
			if (i == 0 && j == 0) {
				fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void export_paths_weight_dis() {
	fopen_s(&fp, "paths_weight_dis.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d\t%d\t%d", i, j, paths_weight_dis[i][j].hops + 1);
			for (k = 0; k < paths_weight_dis[i][j].hops + 1; k++) {
				fprintf_s(fp, "\t%d", paths_weight_dis[i][j].path_nodes[k]);
			}
			if (i == 0 && j == 0) {
				fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void export_paths_weight_dis_links() {
	fopen_s(&fp, "paths_weight_dis_links.txt", "w");
	fprintf_s(fp, "From\tTo\tNum of Nodes\tHops Path\n");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d\t%d\t%d", i, j, paths_weight_dis_links[i][j].hops + 1);
			for (k = 0; k < paths_weight_dis_links[i][j].hops + 1; k++) {
				fprintf_s(fp, "\t%d", paths_weight_dis_links[i][j].path_nodes[k]);
			}
			if (i == 0 && j == 0) {
				fprintf_s(fp, "\t\t\t\t\t\t\t\t\t\t");
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void allocations_export() {
	allocations_weight_protected();
	save_weight_protected();
	allocations_hops_protected();
	save_hops_protected();
	allocations_weight_protected_links();
	save_weight_protected_links();
	allocations_hops_protected_links();
	save_hops_protected_links();
	allocations_weight();
	save_weight();
	allocations_weight_hops();
	save_weight_hops();
	allocations_weight_hops_disjoint();
	save_weight_hops_disjoint();
	allocations_hops();
	save_hops();
	allocations_hops_weight();
	save_hops_weight();
	allocations_hops_weight_disjoint();
	save_hops_weight_disjoint();
}

void print_paths_info() {
	j = 0;
	k = 0;
	for (src = 0; src < nodes; src++) {
		for (dst = 0; dst < nodes; dst++) {
			if (src != dst) {
				if (paths_weight[src][dst].hops == 1)
					j++;
				if (paths_hops[src][dst].hops == 1)
					k++;
				printf("\nMode: Min weight.\n\n");
				printf("Path from %d to %d: %d", src, dst, paths_weight[src][dst].path_nodes[0]);
				hop = paths_weight[src][dst].hops;
				for (i = 1; i <= hop; i++)
					printf(" --> %d", paths_weight[src][dst].path_nodes[i]);
				printf("\nLinks from %d to %d: %d", src, dst, paths_weight[src][dst].path_links[0]);
				for (i = 1; i < hop; i++)
					printf(" --> %d", paths_weight[src][dst].path_links[i]);
				printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_weight[src][dst].mod_format, paths_weight[src][dst].weight);
				printf("\nMode: Min weight disjoint (Nodes).\n\n");
				if (paths_weight_dis[src][dst].exists == 1) {
					printf("Path from %d to %d: %d", src, dst, paths_weight_dis[src][dst].path_nodes[0]);
					hop = paths_weight_dis[src][dst].hops;
					for (i = 1; i <= hop; i++)
						printf(" --> %d", paths_weight_dis[src][dst].path_nodes[i]);
					printf("\nLinks from %d to %d: %d", src, dst, paths_weight_dis[src][dst].path_links[0]);
					for (i = 1; i < hop; i++)
						printf(" --> %d", paths_weight_dis[src][dst].path_links[i]);
					printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_weight_dis[src][dst].mod_format, paths_weight_dis[src][dst].weight);
				}
				else
					printf("Disjoint weight (Nodes) path does not exist.\n");
				printf("\nMode: Min weight disjoint (Links).\n\n");
				if (paths_weight_dis_links[src][dst].exists == 1) {
					printf("Path from %d to %d: %d", src, dst, paths_weight_dis_links[src][dst].path_nodes[0]);
					hop = paths_weight_dis_links[src][dst].hops;
					for (i = 1; i <= hop; i++)
						printf(" --> %d", paths_weight_dis_links[src][dst].path_nodes[i]);
					printf("\nLinks from %d to %d: %d", src, dst, paths_weight_dis_links[src][dst].path_links[0]);
					for (i = 1; i < hop; i++)
						printf(" --> %d", paths_weight_dis_links[src][dst].path_links[i]);
					printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_weight_dis_links[src][dst].mod_format, paths_weight_dis_links[src][dst].weight);
				}
				else
					printf("Disjoint weight (Links) path does not exist.\n");
				printf("\nMode: Min hops.\n\n");
				printf("Path from %d to %d: %d", src, dst, paths_hops[src][dst].path_nodes[0]);
				hop = paths_hops[src][dst].hops;
				for (i = 1; i <= hop; i++)
					printf(" --> %d", paths_hops[src][dst].path_nodes[i]);
				printf("\nLinks from %d to %d: %d", src, dst, paths_hops[src][dst].path_links[0]);
				for (i = 1; i < hop; i++)
					printf(" --> %d", paths_hops[src][dst].path_links[i]);
				printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_hops[src][dst].mod_format, paths_hops[src][dst].weight);
				printf("\nMode: Min hops disjoint (Nodes).\n\n");
				if (paths_hops_dis[src][dst].exists == 1) {
					printf("Path from %d to %d: %d", src, dst, paths_hops_dis[src][dst].path_nodes[0]);
					hop = paths_hops_dis[src][dst].hops;
					for (i = 1; i <= hop; i++)
						printf(" --> %d", paths_hops_dis[src][dst].path_nodes[i]);
					printf("\nLinks from %d to %d: %d", src, dst, paths_hops_dis[src][dst].path_links[0]);
					for (i = 1; i < hop; i++)
						printf(" --> %d", paths_hops_dis[src][dst].path_links[i]);
					printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_hops_dis[src][dst].mod_format, paths_hops_dis[src][dst].weight);
				}
				else
					printf("Disjoint hops (Nodes) path does not exist.\n");
				printf("\nMode: Min hops disjoint (Links).\n\n");
				if (paths_hops_dis_links[src][dst].exists == 1) {
					printf("Path from %d to %d: %d", src, dst, paths_hops_dis_links[src][dst].path_nodes[0]);
					hop = paths_hops_dis_links[src][dst].hops;
					for (i = 1; i <= hop; i++)
						printf(" --> %d", paths_hops_dis_links[src][dst].path_nodes[i]);
					printf("\nLinks from %d to %d: %d", src, dst, paths_hops_dis_links[src][dst].path_links[0]);
					for (i = 1; i < hop; i++)
						printf(" --> %d", paths_hops_dis_links[src][dst].path_links[i]);
					printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_hops_dis_links[src][dst].mod_format, paths_hops_dis_links[src][dst].weight);
				}
				else
					printf("Disjoint hops (Links) path does not exist.\n");
			}
		}
	}
	printf("\nPaths with 1 hops (Weight): %d / %d\n", j,(nodes*nodes)-nodes);
	printf("\nPaths with 1 hops (Hops): %d / %d\n", k, (nodes * nodes) - nodes);
}

void export_slot_contents() {
	fopen_s(&fp, "contents.txt", "w");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d --> %d: ", i, j);
			for (k = 0; k < slotsize; k++) {
				fprintf_s(fp, "%d ", contents[i][j].slots[k]);
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
	fopen_s(&fp, "contentsmatlab.txt", "w");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fprintf_s(fp, "%d \t %d", i, j);
			for (k = 0; k < slotsize; k++) {
				fprintf_s(fp, "\t %d", contents[i][j].slots[k]);
			}
			fprintf_s(fp, "\n");
		}
	}
	fclose(fp);
}

void import_slot_contents() {
	fopen_s(&fp, "contents.txt", "r");
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			fscanf_s(fp, "%d --> %d: ", &i, &j);
			for (k = 0; k < slotsize; k++) {
				fscanf_s(fp, "%d ", &contents[i][j].slots[k]);
			}
		}
	}
	fclose(fp);
}

int find_security(int seccallid) {
	//arxikopiisi
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			xors.callsum[i][j] = 0;
			for (k = 0; k < 250; k++) {
				if (xors.calls[i][j][k] == 0)
					break;
				xors.calls[i][j][k] = 0;
				xors.slots[i][j][k] = 0;
				xors.firstnode[i][j][k] = 0;
				xors.secondnode[i][j][k] = 0;
			}
		}
	}
	// Find security calls
	callid = seccallid;
	//printf("\ncallid=%d", callid);
	src = calls[callid - 1].src;
	dst = calls[callid - 1].dst;
	//printf("\nPath: %d", paths_hops[src][dst].path_nodes[0]);
	//for (i = 0; i < paths_hops[src][dst].hops; i++) {
		//printf(" -> %d", paths_hops[src][dst].path_nodes[i + 1]);
	//}
	//printf("\n\n");
	xors.level = INT_MAX;
	//printf(" %d ", paths_hops[src][dst].hops);
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //for all links
		for (j = 0; j <= i; j++) { //for previous nodes
			//printf("LINK: %d", paths_hops[src][dst].path_nodes[i-j]);
			//r = i-j;
			//while (r <= i) {
				//printf(" -> %d", paths_hops[src][dst].path_nodes[r + 1]);
				//r++;
			//}
			//printf("\n");
			sum = 0;
			for (k = 0; k < nodes; k++) { //for all nodes
				if (k != paths_hops[src][dst].path_nodes[i - j + 1]) {
					for (e = 0; e < slotsize - 1; e++) { //for slots
						if (((contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e] != contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1]) && (contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1] != 0)) || ((e == 0) && (contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e] != 0))) {
							r = k;
							w = 0;
							q = paths_hops[src][dst].path_nodes[i - j];
							first = q;
							second = r;
							if (e == 0) {
								t = contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e];
								e--; //epeidi sto while exw e+1, gia na min xanw to proto slot
							}
							else {
								t = contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1];
							}
							skip = 0;
							while (contents[q][r].slots[e + 1] == t) {
								for (y = 0; y < paths_hops[src][dst].hops; y++) {
									if ((link_id[q][r] == paths_hops[src][dst].path_links[y]) || (link_id[r][q] == paths_hops[src][dst].path_links[y])) { //gia na min xrisimopiisoume idia links me to path
										//printf("\nlink_id[%d][%d] = %d\n", q, r, paths_hops[src][dst].path_links[y]);
										skip = 1;
										break;
									}
									if (skip == 1)
										break;
								}
								if (skip == 0) {
									taken = 0;
									for (y = 0; ((y < nodes) && (taken == 0)); y++) {
										if (contents[r][y].slots[e + 1] == t) {
											taken = 1;
											w = y;
										}
									}
									q = r;
									if (taken == 1) {
										r = w;
									}
									if ((r == paths_hops[src][dst].path_nodes[i + 1]) && (taken == 1) && (contents[q][r].slots[e + 1] != callid)) {
										//printf("can use call %d for security.\n", contents[q][r].slots[e + 1]);
										sum++;
										y = i - j;
										while (y <= i) { // gia kathe link
											taken = 0;
											u = xors.callsum[y][y + 1] - 1;
											while (u >= 0) { //elegxos an yparxei idi to idio call
												if (xors.calls[y][y + 1][u] == contents[q][r].slots[e + 1]) {
													taken = 1;
												}
												u--;
											}
											if (taken == 0) {
												xors.calls[y][y + 1][xors.callsum[y][y + 1]] = contents[q][r].slots[e + 1];
												xors.slots[y][y + 1][xors.callsum[y][y + 1]] = e + 1;
												xors.firstnode[y][y + 1][xors.callsum[y][y + 1]] = first; //for use later when we check slots
												xors.secondnode[y][y + 1][xors.callsum[y][y + 1]] = second;
												xors.callsum[y][y + 1]++;
											}
											y++;
										}
									}
								}
								else {
									break;
								}
								if (q == r)
									t = -1;
							}
						}
						if (e == -1) {
							e++; //apofigi infinite loop
						}
					}
				}
			}
			//printf("\n%d connections available for security.\n\n", sum);
		}
	}
	//Ypologismos Security Level me vasi ta ligotera 
	//for (i = 0; i < paths_hops[src][dst].hops; i++) { //links
		//printf("\nLink %d -> %d: %d connections for security. Calls:", paths_hops[src][dst].path_nodes[i], paths_hops[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
		//for (j = 0; j < xors.callsum[i][i + 1]; j++) { //calls
			//printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
		//}
		//if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			//xors.level = xors.callsum[i][i + 1];
		//}
		//printf("\n\n");
	//}
	//printf("\nSecurity Level for call: %d\n", xors.level);
	//if (xors.level == 0) {
		//printf("\nThis call cannot be secured.\n");
	//}
	//Elegxos slots
	srcslot = calls[callid - 1].startingslot;
	switch (calls[callid - 1].type) {
	case 1:
		dstslot = srcslot + calls[callid - 1].req_slots_weight - 1;
		break;
	case 2:
		dstslot = srcslot + calls[callid - 1].req_slots_weight_dis - 1;
		break;
	case 3:
		dstslot = srcslot + calls[callid - 1].req_slots_weight_dis_links - 1;
		break;
	case 4:
		dstslot = srcslot + calls[callid - 1].req_slots_hops - 1;
		break;
	case 5:
		dstslot = srcslot + calls[callid - 1].req_slots_hops_dis - 1;
		break;
	case 6:
		dstslot = srcslot + calls[callid - 1].req_slots_hops_dis_links - 1;
		break;
	default:
		printf("\n\nCALL IS NOT ALLOCATED.\n\n");
	}
	srcslot = 0;
	dstslot = 310;
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //for links
		r = 0; //counter for calls removed
		for (j = 0; j < xors.callsum[i][i + 1]; j++) { //for calls
			taken = 0;
			k = xors.slots[i][i + 1][j];
			//printf("\ni=%d j=%d k=%d firstnode=%d secondnode=%d firstnode[0][1][0]=%d",i,j,k, xors.firstnode[i][i + 1][j], xors.secondnode[i][i + 1][j],xors.firstnode[0][1][0]);
			while (contents[xors.firstnode[i][i + 1][j]][xors.secondnode[i][i + 1][j]].slots[k] == xors.calls[i][i + 1][j]) { //check all call slots
				for (e = srcslot; e <= dstslot; e++) { //for all req slots
					if (e == k) { //if req slot=call slot, call is valid for security
						taken = 1;
						//printf("\ncall %d is valid for link %d -> %d.", xors.calls[i][i + 1][j], paths_hops[src][dst].path_nodes[i], paths_hops[src][dst].path_nodes[i + 1]);
						break;
					}
					if (taken == 1)
						break;
				}
				if (taken == 1)
					break;
				k++;
			}
			if (taken == 0) { //if the call is not valid
				r++;
				xors.calls[i][i + 1][j] = 0;
			}
		}
		xors.callsum[i][i + 1] = xors.callsum[i][i + 1] - r; //remove invalid calls
	}
	//Print
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //links
		printf("\nLink %d -> %d: %d connections for security. Calls:", paths_hops[src][dst].path_nodes[i], paths_hops[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
		for (j = 0; j < 100; j++) { //calls
			if (xors.calls[i][i + 1][j] != 0) {
				printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
			}
		}
		if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			xors.level = xors.callsum[i][i + 1];
		}
		printf("\n\n");
	}
	printf("\nSecurity Level for call: %d\n", xors.level);
	if (xors.level == 0) {
		printf("\nThis call cannot be secured.\n");
	}
	//Export to file
	fopen_s(&fp, "security.txt", "w");
	fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops[src][dst].hops, srcslot, dstslot, xors.level);
	for (i = 0; i < paths_hops[src][dst].hops; i++) {
		fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
		for (j = 0; j < 100; j++) {
			if (xors.calls[i][i + 1][j] != 0) {
				fprintf_s(fp, "\t%d", xors.calls[i][i + 1][j]);
			}
		}
		fprintf_s(fp, "\n");
	}
	fclose(fp);
	//Export starting slots
	fopen_s(&fp, "securityslots.txt", "w");
	fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops[src][dst].hops, srcslot, dstslot, xors.level);
	for (i = 0; i < paths_hops[src][dst].hops; i++) {
		fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
		for (j = 0; j < 100; j++) {
			if (xors.calls[i][i + 1][j] != 0) {
				fprintf_s(fp, "\t%d", xors.slots[i][i + 1][j]);
			}
		}
		fprintf_s(fp, "\n");
	}
	fclose(fp);
	return (xors.level);
}

int find_security_hops(int seccallid,int mode) {
	//arxikopiisi
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			xors.callsum[i][j] = 0;
			for (k = 0; k < 250; k++) {
				if (xors.calls[i][j][k] == 0)
					break;
				xors.calls[i][j][k] = 0;
				xors.slots[i][j][k] = 0;
				xors.firstnode[i][j][k] = 0;
				xors.secondnode[i][j][k] = 0;
			}
		}
	}
	if (mode == 0) {
		// Eisagogi sta slots
		for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_hops + calls[callid - 1].startingslot; j++) {
				contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
			}
		}
	}
	// Find security calls
	callid = seccallid;
	src = calls[callid - 1].src;
	dst = calls[callid - 1].dst;
	xors.level = INT_MAX;
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //for all links
		for (j = 0; j <= i; j++) { //for previous nodes
			sum = 0;
			for (k = 0; k < nodes; k++) { //for all nodes
				if (k != paths_hops[src][dst].path_nodes[i - j + 1]) {
					for (e = 0; e < slotsize - 1; e++) { //for slots
						if (((contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e] != contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1]) && (contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1] != 0)) || ((e == 0) && (contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e] != 0))) {
							r = k;
							w = 0;
							q = paths_hops[src][dst].path_nodes[i - j];
							first = q;
							second = r;
							if (e == 0) {
								t = contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e];
								e--; //epeidi sto while exw e+1, gia na min xanw to proto slot
							}
							else {
								t = contents[paths_hops[src][dst].path_nodes[i - j]][k].slots[e + 1];
							}
							skip = 0;
							while (contents[q][r].slots[e + 1] == t) {
								for (y = 0; y < paths_hops[src][dst].hops; y++) {
									if ((link_id[q][r] == paths_hops[src][dst].path_links[y]) || (link_id[r][q] == paths_hops[src][dst].path_links[y])) { //gia na min xrisimopiisoume idia links me to path
										skip = 1;
										break;
									}
									if (skip == 1)
										break;
								}
								if (skip == 0) {
									taken = 0;
									for (y = 0; ((y < nodes) && (taken == 0)); y++) {
										if (contents[r][y].slots[e + 1] == t) {
											taken = 1;
											w = y;
										}
									}
									q = r;
									if (taken == 1) {
										r = w;
									}
									if ((r == paths_hops[src][dst].path_nodes[i + 1]) && (taken == 1) && (contents[q][r].slots[e + 1] != callid)) {
										sum++;
										y = i - j;
										while (y <= i) { // gia kathe link
											taken = 0;
											u = xors.callsum[y][y + 1] - 1;
											while (u >= 0) { //elegxos an yparxei idi to idio call
												if (xors.calls[y][y + 1][u] == contents[q][r].slots[e + 1]) {
													taken = 1;
												}
												u--;
											}
											if (taken == 0) {
												xors.calls[y][y + 1][xors.callsum[y][y + 1]] = contents[q][r].slots[e + 1];
												xors.slots[y][y + 1][xors.callsum[y][y + 1]] = e + 1;
												xors.firstnode[y][y + 1][xors.callsum[y][y + 1]] = first; //for use later when we check slots
												xors.secondnode[y][y + 1][xors.callsum[y][y + 1]] = second;
												xors.callsum[y][y + 1]++;
											}
											y++;
										}
									}
								}
								else {
									break;
								}
								if (q == r)
									t = -1;
							}
						}
						if (e == -1) {
							e++; //apofigi infinite loop
						}
					}
				}
			}
		}
	}
	if (mode == 1) {
		i = 0;
		while (i < slotsize) { //gia evresi starting slot
			if (contents[paths_hops[src][dst].path_nodes[0]][paths_hops[src][dst].path_nodes[1]].slots[i] == callid) {
				srcslot = i;
				break;
			}
			i++;
		}
	}
	else {
		srcslot = calls[callid - 1].startingslot;
	}
	dstslot = srcslot + calls[callid - 1].req_slots_hops - 1;
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //for links
		r = 0; //counter for calls removed
		for (j = 0; j < xors.callsum[i][i + 1]; j++) { //for calls
			taken = 0;
			k = xors.slots[i][i + 1][j];
			while (contents[xors.firstnode[i][i + 1][j]][xors.secondnode[i][i + 1][j]].slots[k] == xors.calls[i][i + 1][j]) { //check all call slots
				for (e = srcslot; e <= dstslot; e++) { //for all req slots
					if (e == k) { //if req slot=call slot, call is valid for security
						taken = 1;
						break;
					}
					if (taken == 1)
						break;
				}
				if (taken == 1)
					break;
				k++;
			}
			if (taken == 0) { //if the call is not valid
				r++;
				xors.calls[i][i + 1][j] = 0;
			}
		}
		xors.callsum[i][i + 1] = xors.callsum[i][i + 1] - r; //remove invalid calls
	}
	for (i = 0; i < paths_hops[src][dst].hops; i++) { //links
		if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			xors.level = xors.callsum[i][i + 1];
		}
	}
	if (mode == 0) {
		// Diagrafi apo ta slots
		for (k = 0; k < paths_hops[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_hops + calls[callid - 1].startingslot; j++) {
				contents[paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = 0;
			}
		}
	}
	if (mode == 1) {
		//Print
		for (i = 0; i < paths_hops[src][dst].hops; i++) { //links
			printf("\nLink %d -> %d: %d connections for security. Calls:", paths_hops[src][dst].path_nodes[i], paths_hops[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) { //calls
				if (xors.calls[i][i + 1][j] != 0) {
					printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
				}
			}
			if (xors.callsum[i][i + 1] < xors.level) { //find lowest
				xors.level = xors.callsum[i][i + 1];
			}
			printf("\n\n");
		}
		printf("\nSecurity Level for call: %d\n", xors.level);
		if (xors.level == 0) {
			printf("\nThis call cannot be secured.\n");
		}
		//Export to file
		fopen_s(&fp, "security.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_hops[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.calls[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
		//Export starting slots
		fopen_s(&fp, "securityslots.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_hops[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.slots[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
	}
	return (xors.level);
}

int find_security_weight(int seccallid,int mode) {
	//arxikopiisi
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			xors.callsum[i][j] = 0;
			for (k = 0; k < 250; k++) {
				if (xors.calls[i][j][k] == 0)
					break;
				xors.calls[i][j][k] = 0;
				xors.slots[i][j][k] = 0;
				xors.firstnode[i][j][k] = 0;
				xors.secondnode[i][j][k] = 0;
			}
		}
	}
	if (mode == 0) {
		// Eisagogi sta slots
		for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_weight + calls[callid - 1].startingslot; j++) {
				contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
			}
		}
	}
	// Find security calls
	callid = seccallid;
	src = calls[callid - 1].src;
	dst = calls[callid - 1].dst;
	xors.level = INT_MAX;
	for (i = 0; i < paths_weight[src][dst].hops; i++) { //for all links
		for (j = 0; j <= i; j++) { //for previous nodes
			sum = 0;
			for (k = 0; k < nodes; k++) { //for all nodes
				if (k != paths_weight[src][dst].path_nodes[i - j + 1]) {
					for (e = 0; e < slotsize - 1; e++) { //for slots
						if (((contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e] != contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e + 1]) && (contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e + 1] != 0)) || ((e == 0) && (contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e] != 0))) {
							r = k;
							w = 0;
							q = paths_weight[src][dst].path_nodes[i - j];
							first = q;
							second = r;
							if (e == 0) {
								t = contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e];
								e--; //epeidi sto while exw e+1, gia na min xanw to proto slot
							}
							else {
								t = contents[paths_weight[src][dst].path_nodes[i - j]][k].slots[e + 1];
							}
							skip = 0;
							while (contents[q][r].slots[e + 1] == t) {
								for (y = 0; y < paths_weight[src][dst].hops; y++) {
									if ((link_id[q][r] == paths_weight[src][dst].path_links[y]) || (link_id[r][q] == paths_weight[src][dst].path_links[y])) { //gia na min xrisimopiisoume idia links me to path
										skip = 1;
										break;
									}
									if (skip == 1)
										break;
								}
								if (skip == 0) {
									taken = 0;
									for (y = 0; ((y < nodes) && (taken == 0)); y++) {
										if (contents[r][y].slots[e + 1] == t) {
											taken = 1;
											w = y;
										}
									}
									q = r;
									if (taken == 1) {
										r = w;
									}
									if ((r == paths_weight[src][dst].path_nodes[i + 1]) && (taken == 1) && (contents[q][r].slots[e + 1] != callid)) {
										sum++;
										y = i - j;
										while (y <= i) { // gia kathe link
											taken = 0;
											u = xors.callsum[y][y + 1] - 1;
											while (u >= 0) { //elegxos an yparxei idi to idio call
												if (xors.calls[y][y + 1][u] == contents[q][r].slots[e + 1]) {
													taken = 1;
												}
												u--;
											}
											if (taken == 0) {
												xors.calls[y][y + 1][xors.callsum[y][y + 1]] = contents[q][r].slots[e + 1];
												xors.slots[y][y + 1][xors.callsum[y][y + 1]] = e + 1;
												xors.firstnode[y][y + 1][xors.callsum[y][y + 1]] = first; //for use later when we check slots
												xors.secondnode[y][y + 1][xors.callsum[y][y + 1]] = second;
												xors.callsum[y][y + 1]++;
											}
											y++;
										}
									}
								}
								else {
									break;
								}
								if (q == r)
									t = -1;
							}
						}
						if (e == -1) {
							e++; //apofigi infinite loop
						}
					}
				}
			}
		}
	}
	if (mode == 1) {
		i = 0;
		while (i < slotsize) { //gia evresi starting slot
			if (contents[paths_weight[src][dst].path_nodes[0]][paths_weight[src][dst].path_nodes[1]].slots[i] == callid) {
				srcslot = i;
				break;
			}
			i++;
		}
	}
	else {
		srcslot = calls[callid - 1].startingslot;
	}
	dstslot = srcslot + calls[callid - 1].req_slots_weight - 1;
	for (i = 0; i < paths_weight[src][dst].hops; i++) { //for links
		r = 0; //counter for calls removed
		for (j = 0; j < xors.callsum[i][i + 1]; j++) { //for calls
			taken = 0;
			k = xors.slots[i][i + 1][j];
			while (contents[xors.firstnode[i][i + 1][j]][xors.secondnode[i][i + 1][j]].slots[k] == xors.calls[i][i + 1][j]) { //check all call slots
				for (e = srcslot; e <= dstslot; e++) { //for all req slots
					if (e == k) { //if req slot=call slot, call is valid for security
						taken = 1;
						break;
					}
					if (taken == 1)
						break;
				}
				if (taken == 1)
					break;
				k++;
			}
			if (taken == 0) { //if the call is not valid
				r++;
				xors.calls[i][i + 1][j] = 0;
			}
		}
		xors.callsum[i][i + 1] = xors.callsum[i][i + 1] - r; //remove invalid calls
	}
	for (i = 0; i < paths_weight[src][dst].hops; i++) { //links
		if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			xors.level = xors.callsum[i][i + 1];
		}
	}
	if (mode == 0) {
		// Diagrafi apo ta slots
		for (k = 0; k < paths_weight[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_weight + calls[callid - 1].startingslot; j++) {
				contents[paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = 0;
			}
		}
	}
	if (mode == 1) {
		//Print
		for (i = 0; i < paths_weight[src][dst].hops; i++) { //links
			printf("\nLink %d -> %d: %d connections for security. Calls:", paths_weight[src][dst].path_nodes[i], paths_weight[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) { //calls
				if (xors.calls[i][i + 1][j] != 0) {
					printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
				}
			}
			if (xors.callsum[i][i + 1] < xors.level) { //find lowest
				xors.level = xors.callsum[i][i + 1];
			}
			printf("\n\n");
		}
		printf("\nSecurity Level for call: %d\n", xors.level);
		if (xors.level == 0) {
			printf("\nThis call cannot be secured.\n");
		}
		//Export to file
		fopen_s(&fp, "security.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_weight[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_weight[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.calls[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
		//Export starting slots
		fopen_s(&fp, "securityslots.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_weight[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_weight[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.slots[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
	}
	return (xors.level);
}

int find_security_hops_dis(int seccallid,int mode) {
	//arxikopiisi
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			xors.callsum[i][j] = 0;
			for (k = 0; k < 250; k++) {
				if (xors.calls[i][j][k] == 0)
					break;
				xors.calls[i][j][k] = 0;
				xors.slots[i][j][k] = 0;
				xors.firstnode[i][j][k] = 0;
				xors.secondnode[i][j][k] = 0;
			}
		}
	}
	if (mode == 0) {
		// Eisagogi sta slots
		for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_hops_dis + calls[callid - 1].startingslot; j++) {
				contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
			}
		}
	}
	// Find security calls
	callid = seccallid;
	src = calls[callid - 1].src;
	dst = calls[callid - 1].dst;
	xors.level = INT_MAX;
	for (i = 0; i < paths_hops_dis[src][dst].hops; i++) { //for all links
		for (j = 0; j <= i; j++) { //for previous nodes
			sum = 0;
			for (k = 0; k < nodes; k++) { //for all nodes
				if (k != paths_hops_dis[src][dst].path_nodes[i - j + 1]) {
					for (e = 0; e < slotsize - 1; e++) { //for slots
						if (((contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e] != contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e + 1]) && (contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e + 1] != 0)) || ((e == 0) && (contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e] != 0))) {
							r = k;
							w = 0;
							q = paths_hops_dis[src][dst].path_nodes[i - j];
							first = q;
							second = r;
							if (e == 0) {
								t = contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e];
								e--; //epeidi sto while exw e+1, gia na min xanw to proto slot
							}
							else {
								t = contents[paths_hops_dis[src][dst].path_nodes[i - j]][k].slots[e + 1];
							}
							skip = 0;
							while (contents[q][r].slots[e + 1] == t) {
								for (y = 0; y < paths_hops_dis[src][dst].hops; y++) {
									if ((link_id[q][r] == paths_hops_dis[src][dst].path_links[y]) || (link_id[r][q] == paths_hops_dis[src][dst].path_links[y])) { //gia na min xrisimopiisoume idia links me to path
										skip = 1;
										break;
									}
									if (skip == 1)
										break;
								}
								if (skip == 0) {
									taken = 0;
									for (y = 0; ((y < nodes) && (taken == 0)); y++) {
										if (contents[r][y].slots[e + 1] == t) {
											taken = 1;
											w = y;
										}
									}
									q = r;
									if (taken == 1) {
										r = w;
									}
									if ((r == paths_hops_dis[src][dst].path_nodes[i + 1]) && (taken == 1) && (contents[q][r].slots[e + 1] != callid)) {
										sum++;
										y = i - j;
										while (y <= i) { // gia kathe link
											taken = 0;
											u = xors.callsum[y][y + 1] - 1;
											while (u >= 0) { //elegxos an yparxei idi to idio call
												if (xors.calls[y][y + 1][u] == contents[q][r].slots[e + 1]) {
													taken = 1;
												}
												u--;
											}
											if (taken == 0) {
												xors.calls[y][y + 1][xors.callsum[y][y + 1]] = contents[q][r].slots[e + 1];
												xors.slots[y][y + 1][xors.callsum[y][y + 1]] = e + 1;
												xors.firstnode[y][y + 1][xors.callsum[y][y + 1]] = first; //for use later when we check slots
												xors.secondnode[y][y + 1][xors.callsum[y][y + 1]] = second;
												xors.callsum[y][y + 1]++;
											}
											y++;
										}
									}
								}
								else {
									break;
								}
								if (q == r)
									t = -1;
							}
						}
						if (e == -1) {
							e++; //apofigi infinite loop
						}
					}
				}
			}
		}
	}
	if (mode == 1) {
		i = 0;
		while (i < slotsize) { //gia evresi starting slot
			if (contents[paths_hops_dis[src][dst].path_nodes[0]][paths_hops_dis[src][dst].path_nodes[1]].slots[i] == callid) {
				srcslot = i;
				break;
			}
			i++;
		}
	}
	else {
		srcslot = calls[callid - 1].startingslot;
	}
	dstslot = srcslot + calls[callid - 1].req_slots_hops_dis - 1;
	for (i = 0; i < paths_hops_dis[src][dst].hops; i++) { //for links
		r = 0; //counter for calls removed
		for (j = 0; j < xors.callsum[i][i + 1]; j++) { //for calls
			taken = 0;
			k = xors.slots[i][i + 1][j];
			while (contents[xors.firstnode[i][i + 1][j]][xors.secondnode[i][i + 1][j]].slots[k] == xors.calls[i][i + 1][j]) { //check all call slots
				for (e = srcslot; e <= dstslot; e++) { //for all req slots
					if (e == k) { //if req slot=call slot, call is valid for security
						taken = 1;
						break;
					}
					if (taken == 1)
						break;
				}
				if (taken == 1)
					break;
				k++;
			}
			if (taken == 0) { //if the call is not valid
				r++;
				xors.calls[i][i + 1][j] = 0;
			}
		}
		xors.callsum[i][i + 1] = xors.callsum[i][i + 1] - r; //remove invalid calls
	}
	for (i = 0; i < paths_hops_dis[src][dst].hops; i++) { //links
		if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			xors.level = xors.callsum[i][i + 1];
		}
	}
	if (mode == 0) {
		// Diagrafi apo ta slots
		for (k = 0; k < paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_hops_dis + calls[callid - 1].startingslot; j++) {
				contents[paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_hops_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = 0;
			}
		}
	}
	if (mode == 1) {
		//Print
		for (i = 0; i < paths_hops_dis[src][dst].hops; i++) { //links
			printf("\nLink %d -> %d: %d connections for security. Calls:", paths_hops_dis[src][dst].path_nodes[i], paths_hops_dis[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) { //calls
				if (xors.calls[i][i + 1][j] != 0) {
					printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
				}
			}
			if (xors.callsum[i][i + 1] < xors.level) { //find lowest
				xors.level = xors.callsum[i][i + 1];
			}
			printf("\n\n");
		}
		printf("\nSecurity Level for call: %d\n", xors.level);
		if (xors.level == 0) {
			printf("\nThis call cannot be secured.\n");
		}
		//Export to file
		fopen_s(&fp, "security.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops_dis[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_hops_dis[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.calls[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
		//Export starting slots
		fopen_s(&fp, "securityslots.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_hops_dis[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_hops_dis[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.slots[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
	}
	return (xors.level);
}

int find_security_weight_dis(int seccallid,int mode) {
	//arxikopiisi
	for (i = 0; i < nodes; i++) {
		for (j = 0; j < nodes; j++) {
			xors.callsum[i][j] = 0;
			for (k = 0; k < 250; k++) {
				if (xors.calls[i][j][k] == 0)
					break;
				xors.calls[i][j][k] = 0;
				xors.slots[i][j][k] = 0;
				xors.firstnode[i][j][k] = 0;
				xors.secondnode[i][j][k] = 0;
			}
		}
	}
	if (mode == 0) {
		// Eisagogi sta slots
		for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_weight_dis + calls[callid - 1].startingslot; j++) {
				contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = callid;
			}
		}
	}
	// Find security calls
	callid = seccallid;
	src = calls[callid - 1].src;
	dst = calls[callid - 1].dst;
	xors.level = INT_MAX;
	for (i = 0; i < paths_weight_dis[src][dst].hops; i++) { //for all links
		for (j = 0; j <= i; j++) { //for previous nodes
			sum = 0;
			for (k = 0; k < nodes; k++) { //for all nodes
				if (k != paths_weight_dis[src][dst].path_nodes[i - j + 1]) {
					for (e = 0; e < slotsize - 1; e++) { //for slots
						if (((contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e] != contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e + 1]) && (contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e + 1] != 0)) || ((e == 0) && (contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e] != 0))) {
							r = k;
							w = 0;
							q = paths_weight_dis[src][dst].path_nodes[i - j];
							first = q;
							second = r;
							if (e == 0) {
								t = contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e];
								e--; //epeidi sto while exw e+1, gia na min xanw to proto slot
							}
							else {
								t = contents[paths_weight_dis[src][dst].path_nodes[i - j]][k].slots[e + 1];
							}
							skip = 0;
							while (contents[q][r].slots[e + 1] == t) {
								for (y = 0; y < paths_weight_dis[src][dst].hops; y++) {
									if ((link_id[q][r] == paths_weight_dis[src][dst].path_links[y]) || (link_id[r][q] == paths_weight_dis[src][dst].path_links[y])) { //gia na min xrisimopiisoume idia links me to path
										skip = 1;
										break;
									}
									if (skip == 1)
										break;
								}
								if (skip == 0) {
									taken = 0;
									for (y = 0; ((y < nodes) && (taken == 0)); y++) {
										if (contents[r][y].slots[e + 1] == t) {
											taken = 1;
											w = y;
										}
									}
									q = r;
									if (taken == 1) {
										r = w;
									}
									if ((r == paths_weight_dis[src][dst].path_nodes[i + 1]) && (taken == 1) && (contents[q][r].slots[e + 1] != callid)) {
										sum++;
										y = i - j;
										while (y <= i) { // gia kathe link
											taken = 0;
											u = xors.callsum[y][y + 1] - 1;
											while (u >= 0) { //elegxos an yparxei idi to idio call
												if (xors.calls[y][y + 1][u] == contents[q][r].slots[e + 1]) {
													taken = 1;
												}
												u--;
											}
											if (taken == 0) {
												xors.calls[y][y + 1][xors.callsum[y][y + 1]] = contents[q][r].slots[e + 1];
												xors.slots[y][y + 1][xors.callsum[y][y + 1]] = e + 1;
												xors.firstnode[y][y + 1][xors.callsum[y][y + 1]] = first; //for use later when we check slots
												xors.secondnode[y][y + 1][xors.callsum[y][y + 1]] = second;
												xors.callsum[y][y + 1]++;
											}
											y++;
										}
									}
								}
								else {
									break;
								}
								if (q == r)
									t = -1;
							}
						}
						if (e == -1) {
							e++; //apofigi infinite loop
						}
					}
				}
			}
		}
	}
	if (mode == 1) {
		i = 0;
		while (i < slotsize) { //gia evresi starting slot
			if (contents[paths_weight_dis[src][dst].path_nodes[0]][paths_weight_dis[src][dst].path_nodes[1]].slots[i] == callid) {
				srcslot = i;
				break;
			}
			i++;
		}
	}
	else {
		srcslot = calls[callid - 1].startingslot;
	}
	dstslot = srcslot + calls[callid - 1].req_slots_weight_dis - 1;
	for (i = 0; i < paths_weight_dis[src][dst].hops; i++) { //for links
		r = 0; //counter for calls removed
		for (j = 0; j < xors.callsum[i][i + 1]; j++) { //for calls
			taken = 0;
			k = xors.slots[i][i + 1][j];
			while (contents[xors.firstnode[i][i + 1][j]][xors.secondnode[i][i + 1][j]].slots[k] == xors.calls[i][i + 1][j]) { //check all call slots
				for (e = srcslot; e <= dstslot; e++) { //for all req slots
					if (e == k) { //if req slot=call slot, call is valid for security
						taken = 1;
						break;
					}
					if (taken == 1)
						break;
				}
				if (taken == 1)
					break;
				k++;
			}
			if (taken == 0) { //if the call is not valid
				r++;
				xors.calls[i][i + 1][j] = 0;
			}
		}
		xors.callsum[i][i + 1] = xors.callsum[i][i + 1] - r; //remove invalid calls
	}
	for (i = 0; i < paths_weight_dis[src][dst].hops; i++) { //links
		if (xors.callsum[i][i + 1] < xors.level) { //find lowest
			xors.level = xors.callsum[i][i + 1];
		}
	}
	if (mode == 0) {
		// Diagrafi apo ta slots
		for (k = 0; k < paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].hops; k++) {
			for (j = calls[callid - 1].startingslot; j < calls[callid - 1].req_slots_weight_dis + calls[callid - 1].startingslot; j++) {
				contents[paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k]][paths_weight_dis[calls[callid - 1].src][calls[callid - 1].dst].path_nodes[k + 1]].slots[j] = 0;
			}
		}
	}
	if (mode == 1) {
		//Print
		for (i = 0; i < paths_weight_dis[src][dst].hops; i++) { //links
			printf("\nLink %d -> %d: %d connections for security. Calls:", paths_weight_dis[src][dst].path_nodes[i], paths_weight_dis[src][dst].path_nodes[i + 1], xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) { //calls
				if (xors.calls[i][i + 1][j] != 0) {
					printf("\t%d[%d]", xors.calls[i][i + 1][j], xors.slots[i][i + 1][j]);
				}
			}
			if (xors.callsum[i][i + 1] < xors.level) { //find lowest
				xors.level = xors.callsum[i][i + 1];
			}
			printf("\n\n");
		}
		printf("\nSecurity Level for call: %d\n", xors.level);
		if (xors.level == 0) {
			printf("\nThis call cannot be secured.\n");
		}
		//Export to file
		fopen_s(&fp, "security.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_weight_dis[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_weight_dis[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.calls[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
		//Export starting slots
		fopen_s(&fp, "securityslots.txt", "w");
		fprintf_s(fp, "%d\t%d\t%d\t%d\t%d\t%d\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\t\n", src, dst, paths_weight_dis[src][dst].hops, srcslot, dstslot, xors.level);
		for (i = 0; i < paths_weight_dis[src][dst].hops; i++) {
			fprintf_s(fp, "%d", xors.callsum[i][i + 1]);
			for (j = 0; j < 100; j++) {
				if (xors.calls[i][i + 1][j] != 0) {
					fprintf_s(fp, "\t%d", xors.slots[i][i + 1][j]);
				}
			}
			fprintf_s(fp, "\n");
		}
		fclose(fp);
	}
	return (xors.level);
}

void find_security_level() {
	FILE* fp2;
	int g;
	int levels[10]{};
	fopen_s(&fp2, "security_levels.txt", "w");
	int path1,level1,sum1=0;
	for (g = 0; g < call_amount; g++) {
		//printf("\ni= %d", i);
		path1 = calls[g].type;
		switch (path1) {
		case 4:
			level1 = find_security_hops(g+1, 1);
			break;
		case 1:
			level1 = find_security_weight(g+1, 1);
			break;
		case 5:
			level1 = find_security_hops_dis(g+1, 1);
			break;
		case 2:
			level1 = find_security_weight_dis(g+1, 1);
			break;
		default:
			level1 = -1;
			printf("\nFAIL\n");
		}
		if (level1 >= 0)
			levels[level1]++;
		if (level1 > 0)
			sum1++;
		fprintf_s(fp2, "Callid: %d\tSecurity Level: %d\n", g + 1, level1);
	}
	fprintf_s(fp2, "%d calls secured of %d.", sum1, call_amount);
	for (i=0;i<10;i++)
		fprintf_s(fp2, "\nCalls with Security Level %d: %d",i,levels[i]);
	fclose(fp2);
}

int main() {
	fopen_s(&fp, "requests_sample.txt", "r");
	if (fp == NULL) {
		printf("Could not open file.\n");
		return 0;
	}
	fscanf_s(fp, "%d", &nodes);
	int callsid;
	read_graph();
	//print_graph();
	make_slots();
	make_link_id();
	fopen_s(&fp, "arguments.txt", "r");
	fscanf_s(fp, "%d", &callsid);
	fscanf_s(fp, "%d", &step);
	fscanf_s(fp, "%d", &securitycallid);
	fclose(fp);
	snprintf(filename, sizeof(filename), "Requests\\requests-%d.txt", callsid);
	paths_weight = new path_info * [nodes];
	paths_weight_dis = new path_info * [nodes];
	paths_weight_dis_links = new path_info * [nodes];
	paths_hops = new path_info * [nodes];
	paths_hops_dis = new path_info * [nodes];
	paths_hops_dis_links = new path_info * [nodes];
	graphtemp = new int* [nodes];
	for (i = 0; i < nodes; i++) {
		graphtemp[i] = new int[nodes] {};
	}
	for (i = 0; i < nodes; i++) {
		paths_weight[i] = new path_info[nodes];
		paths_weight_dis[i] = new path_info[nodes];
		paths_weight_dis_links[i] = new path_info[nodes];
		paths_hops[i] = new path_info[nodes];
		paths_hops_dis[i] = new path_info[nodes];
		paths_hops_dis_links[i] = new path_info[nodes];
		for (j = 0; j < nodes; j++) {
			paths_weight[i][j].path_nodes = new int[nodes] {};
			paths_weight[i][j].path_links = new int[nodes] {};
			paths_weight_dis[i][j].path_nodes = new int[nodes] {};
			paths_weight_dis[i][j].path_links = new int[nodes] {};
			paths_weight_dis_links[i][j].path_nodes = new int[nodes] {};
			paths_weight_dis_links[i][j].path_links = new int[nodes] {};
			paths_hops[i][j].path_nodes = new int[nodes] {};
			paths_hops[i][j].path_links = new int[nodes] {};
			paths_hops_dis[i][j].path_nodes = new int[nodes] {};
			paths_hops_dis[i][j].path_links = new int[nodes] {};
			paths_hops_dis_links[i][j].path_nodes = new int[nodes] {};
			paths_hops_dis_links[i][j].path_links = new int[nodes] {};
		}
	}
	// Memory Allocation for security
	xors.calls = new int** [nodes];
	xors.slots = new int** [nodes];
	xors.firstnode = new int** [nodes];
	xors.secondnode = new int** [nodes];
	xors.callsum = new int* [nodes];
	for (i = 0; i < nodes; i++) { //arxikopiisi xors
		xors.callsum[i] = new int[nodes] {};
		xors.calls[i] = new int* [nodes];
		xors.slots[i] = new int* [nodes];
		xors.firstnode[i] = new int* [nodes];
		xors.secondnode[i] = new int* [nodes];
		for (j = 0; j < nodes; j++) {
			xors.calls[i][j] = new int[250]{};
			xors.slots[i][j] = new int[250]{};
			xors.firstnode[i][j] = new int[250]{};
			xors.secondnode[i][j] = new int[250]{};
		}
	}
	make_paths_table();
	make_calls_table();
	allocations = new allocation_info[call_amount / step];
	//allocations_export(); //For matlab graph
	//print_paths_info();
	export_paths_hops();
	export_paths_hops_dis();
	export_paths_hops_dis_links();
	export_paths_weight();
	export_paths_weight_dis();
	export_paths_weight_dis_links();
	//import_paths_used();
	path = calls[securitycallid - 1].type;
	//printf("\nPath= %d", path);
	//path = 0;
	//allocations_bestfit();
	//export_slot_contents();
	//export_paths_used();
	//import_slot_contents();
	//find_security_level();
	switch (path) {
	case 4:
		find_security_hops(securitycallid, 1);
		break;
	case 1:
		find_security_weight(securitycallid, 1);
		break;
	case 5:
		find_security_hops_dis(securitycallid, 1);
		break;
	case 2:
		find_security_weight_dis(securitycallid, 1);
		break;
	default:
		printf("\nFAIL\n");
		//allocations_bestfit();
		//export_slot_contents();
		//export_paths_used();
	}
	while (choice != 6) {
		printf("\n1. Show paths.\n2. Print info.\n3. Print Calls info.\n4. Spectrum Allocation for calls & export to txt.\n5. Export slot contents to file.\n6. Exit.\n\nInsert your choice: ");
		scanf_s("%d", &choice);
		while (choice < 1 || choice>6) {
			printf("Invalid choice. Insert again: ");
			scanf_s("%d", &choice);
		}
		if (choice == 1) { //Find shortest path
			printf("Insert source node: ");
			scanf_s("%d", &src);
			while (src < 0 || src >= nodes) {
				printf("Invalid node. Insert again: ");
				scanf_s("%d", &src);
			}
			printf("Insert destination node: ");
			scanf_s("%d", &dst);
			while (dst < 0 || dst >= nodes) {
				printf("Invalid node. Insert again: ");
				scanf_s("%d", &dst);
			}
			printf("\nMode: Min weight.\n\n");
			printf("Path from %d to %d: %d", src, dst, paths_weight[src][dst].path_nodes[0]);
			hop = paths_weight[src][dst].hops;
			for (i = 1; i <= hop; i++)
				printf(" --> %d", paths_weight[src][dst].path_nodes[i]);
			printf("\nLinks from %d to %d: %d", src, dst, paths_weight[src][dst].path_links[0]);
			for (i = 1; i < hop; i++)
				printf(" --> %d", paths_weight[src][dst].path_links[i]);
			printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_weight[src][dst].mod_format, paths_weight[src][dst].weight);
			printf("\nMode: Min weight disjoint.\n\n");
			if (paths_weight_dis[src][dst].exists == 1) {
				printf("Path from %d to %d: %d", src, dst, paths_weight_dis[src][dst].path_nodes[0]);
				hop = paths_weight_dis[src][dst].hops;
				for (i = 1; i <= hop; i++)
					printf(" --> %d", paths_weight_dis[src][dst].path_nodes[i]);
				printf("\nLinks from %d to %d: %d", src, dst, paths_weight_dis[src][dst].path_links[0]);
				for (i = 1; i < hop; i++)
					printf(" --> %d", paths_weight_dis[src][dst].path_links[i]);
				printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_weight_dis[src][dst].mod_format, paths_weight_dis[src][dst].weight);
			}
			else
				printf("Disjoint weight path does not exist.\n");
			printf("\nMode: Min hops.\n\n");
			printf("Path from %d to %d: %d", src, dst, paths_hops[src][dst].path_nodes[0]);
			hop = paths_hops[src][dst].hops;
			for (i = 1; i <= hop; i++)
				printf(" --> %d", paths_hops[src][dst].path_nodes[i]);
			printf("\nLinks from %d to %d: %d", src, dst, paths_hops[src][dst].path_links[0]);
			for (i = 1; i < hop; i++)
				printf(" --> %d", paths_hops[src][dst].path_links[i]);
			printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_hops[src][dst].mod_format, paths_hops[src][dst].weight);
			printf("\nMode: Min hops disjoint.\n\n");
			if (paths_hops_dis[src][dst].exists == 1) {
				printf("Path from %d to %d: %d", src, dst, paths_hops_dis[src][dst].path_nodes[0]);
				hop = paths_hops_dis[src][dst].hops;
				for (i = 1; i <= hop; i++)
					printf(" --> %d", paths_hops_dis[src][dst].path_nodes[i]);
				printf("\nLinks from %d to %d: %d", src, dst, paths_hops_dis[src][dst].path_links[0]);
				for (i = 1; i < hop; i++)
					printf(" --> %d", paths_hops_dis[src][dst].path_links[i]);
				printf("\nHops: %d\nMod Format: %d\nWeight: %d\n", hop, paths_hops_dis[src][dst].mod_format, paths_hops_dis[src][dst].weight);
			}
			else
				printf("Disjoint hops path does not exist.\n");
		}
		else if (choice == 2) { //Print info
			printf("\n1. Print info about graph.\n2. Print Link ID Table.\n3. Back.\n\nInsert your choice: ");
			scanf_s("%d", &choice);
			while (choice < 1 || choice>3) {
				printf("Invalid choice. Insert again: ");
				scanf_s("%d", &choice);
			}
			if (choice == 1) {
				print_graph();
				printf("Nodes: %d\n", nodes);
				printf("Bandwidth: %d\n", bandwidth);
				printf("Spacing: %d\n", spacing);
				printf("Slot size: %d\n", slotsize);
			}
			else if (choice == 2) {
				print_link_id();
			}
			choice = 1;
		}
		else if (choice == 3) { //Print calls info
			printf("\nCall ID\tSource\tDest\tReq Bwdth\tSlots Weight\tSlots Hops\tSlots Weight Dis\tSlots Hops Dis\n\n");
			for (i = 0; i < call_amount; i++) {
				printf("%d\t%d\t%d\t%d\t\t%d\t\t%d\t\t%d\t\t\t%d\n", calls[i].req_id, calls[i].src, calls[i].dst, calls[i].req, calls[i].req_slots_weight, calls[i].req_slots_hops, calls[i].req_slots_weight_dis, calls[i].req_slots_hops_dis);
			}
		}
		else if (choice == 4) { //Spectrum Allocation for calls + export to file
			printf("\nInsert Step: ");
			scanf_s("%d", &step);
			allocations = new allocation_info[call_amount / step];
			allocations_weight_hops_disjoint();
			save_weight_hops_disjoint();
			allocations_weight_hops();
			save_weight_hops();
			allocations_weight();
			save_weight();
			allocations_hops_weight_disjoint();
			save_hops_weight_disjoint();
			allocations_hops_weight();
			save_hops_weight();
			allocations_hops();
			save_hops();
		}
		else if (choice == 5) { //Export slot contents to file
		fopen_s(&fp, "contents.txt", "w");
		for (i = 0; i < nodes; i++) {
			for (j = 0; j < nodes; j++) {
				//if (graph[i][j] != 0) {
					fprintf_s(fp, "%d --> %d: ", i, j);
					for (k = 0; k < slotsize; k++) {
						fprintf_s(fp, "%d ", contents[i][j].slots[k]);
					}
					fprintf_s(fp, "\n");
				//}
			}
		}
		fclose(fp);
		}
	}
	return 0;
}