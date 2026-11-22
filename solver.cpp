//============================================================================
// Name        : IRMS.cpp
// Author      : 
// Version     :
// Copyright   : Your copyright notice
// Description : Instance Reduction based Memetic Search for CNP
//============================================================================

#include <stdlib.h>
#include <math.h>
#include <fstream>
#include <iostream>
#include <unistd.h>
#include <time.h>
#include <string.h>
#include <limits.h>
#include <algorithm>
using namespace std;

unsigned cnp_clock();	// clock in seconds used for seeding (defined in host_main.cpp)

#define ADD(s,x,index_x,nbr_x)(x[nbr_x] = s,index_x[s] = nbr_x++)
#define EPS 0.000001
#define GEO_QMAX 0.5
#define ALPHA 0.60
#define BETA 0.90
#define THETA 0.3
#define PS 5
#define MAX_IDLE_STEPS 1000
#define OSC_P 0.1
#define OSC_DMAX 3
double DegP = 0.0;	// set in setup_data: 0.5*min(1, 4*CV^2 of the degrees)

// running time
double StartTime,ImprovedTime,BestTime,build_time;
int FixedAllocatedSpace;
double LimitTime;
long unsigned BestNbrGens;

// instance
char *InstanceName; 			// instance file name
char *Dataset;					// data set
char ResultPath[100]; 			// result file path
char StatisticPath[100];		// statistical file path
char InstancePath[100];			// instance file path
int NbrRepeats;

int NbrV,NbrE;
int NbrC,ImprovedNbrC,BestNbrC;
int K; // maximum number of removed nodes
int *Node;

int **AdjacencyList;
int **Components,*VInComponent,*IndexVInComponent;
int *LargeComponentList;
int *RemovedV,*ImprovedRemovedV,*BestRemovedV,*ReducedV;
int *IndexRemovedV;
int NbrRemovedV,NbrImprovedRemovedV,NbrBestRemovedV,NbrReducedV;
int *List,*VList,*IndexVInVList;
bool *IsMarked;
int *UsedV;
int *VAge;
int *ReduceFlag;
int *PoolV,NbrPoolV;	// parents' removed vertices left free by the reduction
char *ParentMask;	// bit0: removed in parent A, bit1: removed in parent B
int *RegStamp, CurRegStamp = 0, *RegQueue;	// geographic crossover region (BFS ball)
int *RegCell, *CellSide; double ParentCostAvg = 0;

int ObjValue,ImprovedObjValue,BestObjValue;
int BKV;	// best known value
bool OF;	// indicate the KBV is optimal or not

// Population
int **Pop;
double *PopCost;
double **SolSimilarity;
double *PopSimilarity;
double *PopScore;

// Tarjan
int *dfn;
int *low;
int *st_size;
int *cut_size;
int *impact;
int *flag;
bool *is_cut;
int time_stamp;
int root;
int Component;

void REMOVE(int s,int *x,int *index_x,int &nbr_x)
{
	register int *p0 = x;
	register int *p1 = &index_x[s];
	*(p0 + *p1) = *(p0 + (--nbr_x));
	*(index_x + *(p0 + nbr_x)) = *p1;
	*p1 = -1;
}

// stamp-based marking (avoids O(n) resets)
int *MarkStamp; int CurStamp = 0;
int *DfsStack;
static inline void new_stamp()
{
	if(++CurStamp == INT_MAX)
	{
		for(int i = 0; i < NbrV; i++) MarkStamp[i] = 0;
		CurStamp = 1;
	}
}

int depth_first_search(int v,int *list)
{
	new_stamp();
	list[0] = 0;
	int top = 0;
	DfsStack[top++] = v;
	MarkStamp[v] = CurStamp;
	while(top)
	{
		int x = DfsStack[--top];
		list[++list[0]] = x;
		int *adj = AdjacencyList[x];
		int d = adj[0];
		for(int i = 1; i <= d; i++)
		{
			int w = adj[i];
			if(IndexRemovedV[w] == -1 && MarkStamp[w] != CurStamp)
			{
				MarkStamp[w] = CurStamp;
				DfsStack[top++] = w;
			}
		}
	}
	return list[0];
}

void tarjan_in_component(int x){
	dfn[x] = low[x] = ++time_stamp;
    int current_x = Components[Component][x];
    int *p = &AdjacencyList[current_x][1];
    for(int i = 1; i <= AdjacencyList[current_x][0]; i++,p++)
    {
    	int temp = *p;
    	if(IndexRemovedV[temp] == -1)
    	{
    		int index = IndexVInComponent[temp];
            if(!dfn[index]){         //not be visited
            	tarjan_in_component(index);
                low[x] = min(low[x], low[index]);
                if(dfn[x] < dfn[index])
                	st_size[x] = st_size[x] + st_size[index];
                if(low[index] >= dfn[x]) {   //if x is a cut node
                    flag[x]++;
            	    if(x != root)
            	    {
            		    is_cut[x] = true;
            		    cut_size[x] = cut_size[x] + st_size[index];
            		    impact[x] = impact[x] + (st_size[index]*(st_size[index]-1))/2;
            	    }
            	    else if(x == root && flag[x] > 1)
            	    	is_cut[x] = true;
                }
            }
            else
        	    low[x] = min(low[x], dfn[index]);
    	}
    }
}

// Sort the elements in the solution in am ascend order
void ascend_sort(int *sol)
{
     int count = 0;
     memset(UsedV,0,FixedAllocatedSpace);

     for(int i = 0; i < K; i++)
    	 UsedV[sol[i]] = 1;

     for(int i = 0; i < NbrV; i++)
    	 if(UsedV[Node[i]] == 1)
    		 sol[count++] = Node[i];
}

// Check the solution is duplicate or not in the population
bool is_duplicate_sol(int index_sol)
{
    bool duplicate = false;
    for(int i = 0; i < index_sol; i++)
    {
    	duplicate = true;
    	for(int j = 0; j < K; j++)
    		if(ImprovedRemovedV[j] != Pop[i][j])
    		{
    			duplicate = false;
    			break;
    		}

    	if(duplicate == true)
    		break;
    }
    return duplicate;
}

// Compute the distance between any two solutions in the population
double compute_SolSimilarity(int x1,int x2)
{
	double sol_similarity;
	int u = 0;
	int v = 0;
    int nbr_sharing_v = 0;
    while((u < K) && (v < K))
    {
    	if(Pop[x1][u] == Pop[x2][v])
    	{
    		nbr_sharing_v++;
    		u++;
    		v++;
    	}
    	else if(Pop[x1][u] < Pop[x2][v])
    		u++;
        else if(Pop[x1][u] > Pop[x2][v])
        	v++;
    }
    sol_similarity = (double)nbr_sharing_v/(double)NbrV;
    return sol_similarity;
}

void calculate_its_rank(int index,int nbr,double *x1,int *x2)
{
	double *x;
	x = new double[nbr];
	for(int i = 0; i < nbr; i++)
		x[i] = x1[i];

	int *flag;
	flag = new int[nbr];
	for(int i = 0; i < nbr; i++)
		flag[i] = 0;

	double temp;
    for(int i = 1; i < nbr; i++)
    	for(int j = nbr-1; j >= i; j--)
        {
    		if(index == 0)
    		{
    			// lower score, lower rank
    			if(x[j-1] > x[j])
    			{
    				temp = x[j-1];
    				x[j-1] = x[j];
    				x[j] = temp;
    			}
    		}
    		else if(index == 1)
    		{
    			// higher score, lower rank
    			if(x[j-1] < x[j])
    			{
    				temp = x[j-1];
    				x[j-1] = x[j];
    				x[j] = temp;
    			}
    		}
        }

    for(int i = 0; i < nbr; i++)
    	for(int j = 0; j < nbr; j++)
    	{
    		if(flag[j] == 0 && x1[i] == x[j])
    		{
    			x2[i] = j + 1;
    			flag[j] = 1;
    			break;
    		}
    	}
    delete [] x;
    delete [] flag;
}

/* Verify and store the results */
void store_result(char *result_file_path, int repeat)
{
	FILE *res;
	// Store the results
	if((res = fopen(result_file_path,"a+")) == NULL)
    {
		printf("Open failed for output  %s\n",result_file_path);
		exit(1);
    }
	fprintf(res,"   -----------------------------------------------------\n");
	fprintf(res,"   Repeat = %d\n",repeat);
	fprintf(res,"   -----------------------------------------------------\n");
	fprintf(res,"   best objective value = %d\n",BestObjValue);
	fprintf(res,"   time to find the best objective value = %f\n",BestTime);
	fprintf(res,"   number of generations to find the objective value = %ld\n",BestNbrGens);
	fprintf(res,"   Best removed nodes:\n");
	for(int i = 0; i < NbrBestRemovedV; i++)
		fprintf(res,"%d ",BestRemovedV[i]);
	fprintf(res,"\n");

	fclose(res);
}

/* Verify the results */
void check_result(int *removed_v,int nbr_removed_v,int obj_value,int nbr_c)
{
	int true_obj_value = 0;
	int true_nbr_c = 0;

	bool *is_visited;
	is_visited = new bool[NbrV];
	for(int i = 0; i < NbrV; i++)
		is_visited[i] = false;

	for(int i = 0; i < NbrV; i++)
		IndexRemovedV[i] = -1;
	for(int i = 0; i < nbr_removed_v; i++)
		IndexRemovedV[removed_v[i]] = 0;

	for(int i = 0; i < NbrV; i++)
		if(!is_visited[i] && IndexRemovedV[i] == -1)
		{
			depth_first_search(i,List);
			true_nbr_c++;
			for(int j = 1; j <= List[0]; j++)
				is_visited[List[j]] = true;
			true_obj_value += List[0]*(List[0]-1)/2;
		}

	if(nbr_c != true_nbr_c || true_obj_value != obj_value)
	{
		printf("The solution is not correct!\n");
		printf("nbr_c = %d, its true value = %d\n",nbr_c,true_nbr_c);
		printf("obj_value = %d, its true value = %d\n",obj_value,true_obj_value);
		exit(-1);
	}

	if(nbr_removed_v != K)
	{
		printf("K = %d, while the number of removed nodes is %d\n",K,nbr_removed_v);
		exit(-1);
	}
	delete[] is_visited;
}

int select_remove_larger_component()
{
	int avg_c_size = int(float(NbrV-NbrRemovedV)/float(NbrC) + 0.5);
	if(avg_c_size < 2)
		avg_c_size = 2;

	int total_nbr_v_in_big_c = 0;
	LargeComponentList[0] = 0;
	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] > avg_c_size)
		{
			LargeComponentList[++LargeComponentList[0]] = i;
			total_nbr_v_in_big_c += Components[i][0];
		}

	if(LargeComponentList[0] == 1)
	{
		if(rand()%2)
		{
			int best2C = 0,bestC = LargeComponentList[1];
			int max_size_c = Components[0][0];
			for(int i = 1; i < NbrC; i++)
				if(i != bestC && Components[i][0] > max_size_c)
				{
					max_size_c = Components[i][0];
					best2C = i;
				}
			return best2C;
		}
		else
			return LargeComponentList[1];
	}

	int index = rand()%total_nbr_v_in_big_c;
	int sum = 0,sum1 = Components[LargeComponentList[1]][0];
	for(int i = 1; i <= LargeComponentList[0]; i++)
	{
		if(index >= sum && index <= sum1)
			return LargeComponentList[i];
		sum = sum1;
		sum1 += Components[LargeComponentList[i+1]][0];
	}

	return LargeComponentList[LargeComponentList[0]];
}

// return a larger component
int select_remove_component()
{
	int min_size_c = NbrV,max_size_c = 0;
	if(NbrC > 50)
		return select_remove_larger_component();

	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] > 2)
		{
			if(Components[i][0] < min_size_c)
				min_size_c = Components[i][0];
			if(Components[i][0] > max_size_c)
				max_size_c = Components[i][0];
		}
	float c_size_threshold = max_size_c-(max_size_c-min_size_c)*0.5-rand()%3;

	LargeComponentList[0] = 0;
	for(int i = 0; i < NbrC; i++)
		if(Components[i][0] >= c_size_threshold)
			LargeComponentList[++LargeComponentList[0]] = i;

	return LargeComponentList[rand()%LargeComponentList[0]+1];
}

// randomly select a node
int select_remove_node_at_random(int c)
{
	int index = rand()%Components[c][0] + 1;
	return Components[c][index];
}

// degree-biased proposal (offer S2_v9): random in-component neighbour of a random vertex of c
int select_remove_node_by_degree(int c)
{
	int x = Components[c][rand()%Components[c][0] + 1];
	const int *adj = AdjacencyList[x];
	int pick = x, cnt = 0;
	for(int j = 1; j <= adj[0]; j++)
		if(VInComponent[adj[j]] == c && rand()%(++cnt) == 0) pick = adj[j];
	return pick;
}

int *CandBuf;
int select_remove_node_with_weight(int c)
{
	int choose_v;
	int v;
	int *candidate_v = CandBuf;
	int nbr_candidate_v;
	int min_age = INT_MAX;

	for(int i = 1; i <= Components[c][0]; i++)
	{
		v = Components[c][i];
		if(VAge[v] < min_age)
		{
			min_age = VAge[v];
			candidate_v[0] = v;
			nbr_candidate_v = 1;
		}
		else if(VAge[v] == min_age)
		{
			candidate_v[nbr_candidate_v] = v;
			nbr_candidate_v++;
		}
	}
	choose_v = candidate_v[rand()%nbr_candidate_v];
	return choose_v;
}

// fast exact Tarjan: per-vertex records, global DFS clock (visited iff dfn > base), no per-call init
struct TjNode { int dfn, low, st, cut, imp, flg, it; };
TjNode *TjN; int *TjStack, *TjBest; long TjClock = 0;
// offer S2_v3 (carving): no cut vertex in c (every pick is equivalent for the impact rule). Take the vertex x
// of c with the fewest neighbours inside c and remove one of them, driving x toward detachment.
// AliveDeg[x] = number of non-removed neighbours of x (= in-component degree of an alive x), maintained by
// remove_node/add_node while valid; invalidated by every component rebuild (create_a_component), rebuilt lazily.
int *AliveDeg = 0; bool AliveDegValid = false; int NTotalV = 0;
static void rebuild_alive_deg()
{
	for(int x = 0; x < NTotalV; x++)
	{
		const int *adj = AdjacencyList[x];
		int d = 0;
		for(int j = 1; j <= adj[0]; j++)
			if(IndexRemovedV[adj[j]] == -1) d++;
		AliveDeg[x] = d;
	}
	AliveDegValid = true;
}
static int carve_pick(int c)
{
	int n = Components[c][0];
	int *comp = Components[c];
	int min_d = INT_MAX, x = -1, nt = 0;
	if(!AliveDegValid) rebuild_alive_deg();
	for(int i = 1; i <= n; i++)
	{
		int y = comp[i];
		int d = AliveDeg[y];
		if(d < min_d) { min_d = d; x = y; nt = 1; }
		else if(d == min_d && rand()%(++nt) == 0) x = y;
	}
	const int *adj = AdjacencyList[x];
	int pick = -1, cnt = 0;
	for(int j = 1; j <= adj[0]; j++)
		if(VInComponent[adj[j]] == c && rand()%(++cnt) == 0) pick = adj[j];
	return pick;
}
static inline unsigned long long splitmix64(unsigned long long &x)
{
	unsigned long long z = (x += 0x9E3779B97F4A7C15ULL);
	z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
	z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
	return z ^ (z >> 31);
}
#define BICON_MEMO_SIZE (1<<16)
#define MEMO_MAXV 16
struct TjMemo { unsigned long long key; int cnt; int v[MEMO_MAXV]; };	// cnt 0: no cut vertex; else min-impact vertices
unsigned long long *ZKey = 0; TjMemo *BiconMemo = 0; long BiconHits = 0, BiconMiss = 0;
int select_remove_node_with_impact(int c)
{
	int n = Components[c][0];
	int *comp = Components[c];
	if(TjClock > 2000000000L - 2L*NbrV)
	{
		for(int i = 0; i < FixedAllocatedSpace/(int)sizeof(int); i++) TjN[i].dfn = 0;
		TjClock = 0;
	}
	const int rt = comp[1];
	// exact memo: the cut structure of a component depends only on its vertex set (induced subgraph) and,
	// for the root quirk, on the DFS root; sets already found to have no (non-root) cut vertex skip Tarjan.
	unsigned long long hkey = 0;
	if(n > 3)
	{
		if(!ZKey)
		{
			int sz = FixedAllocatedSpace/(int)sizeof(int);
			ZKey = new unsigned long long[sz];
			unsigned long long z = 0x2545F4914F6CDD1DULL;
			for(int i = 0; i < sz; i++) ZKey[i] = splitmix64(z);
			BiconMemo = new TjMemo[BICON_MEMO_SIZE]();
		}
		for(int i = 1; i <= n; i++) hkey ^= ZKey[comp[i]];
		unsigned long long zr = (unsigned long long)rt*0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
		hkey ^= splitmix64(zr);
		if(hkey == 0) hkey = 1;
		TjMemo &me = BiconMemo[hkey & (BICON_MEMO_SIZE-1)];
		if(me.key == hkey)
		{
			BiconHits++;
			if(me.cnt == 0)
			{
				int choose_i = rand()%n + 1;
				int pick = carve_pick(c);
				if(pick >= 0) return pick;
				return comp[choose_i];
			}
			// min-impact vertices in their current order in comp (as the scan would list them)
			int m = me.cnt, tmp[MEMO_MAXV];
			for(int a = 0; a < m; a++) tmp[a] = me.v[a];
			for(int a = 1; a < m; a++)
			{
				int x = tmp[a], b = a - 1;
				while(b >= 0 && IndexVInComponent[tmp[b]] > IndexVInComponent[x]) { tmp[b+1] = tmp[b]; b--; }
				tmp[b+1] = x;
			}
			return tmp[rand()%m];
		}
	}
	BiconMiss++;
	const int base = (int)TjClock;
	int ts = base;
	int top = 0;
	{
		TjNode &r = TjN[rt];
		r.dfn = r.low = ++ts; r.st = 1; r.cut = 1; r.imp = 0; r.flg = 0; r.it = 1;
	}
	TjStack[top++] = rt;
	while(top)
	{
		int x = TjStack[top-1];
		TjNode &nx = TjN[x];
		const int *adj = AdjacencyList[x];
		const int deg = adj[0];
		int it = nx.it;
		int pushed = -1;
		while(it <= deg)
		{
			int w = adj[it++];
			if(IndexRemovedV[w] != -1) continue;
			TjNode &nw = TjN[w];
			if(nw.dfn <= base)
			{
				nw.dfn = nw.low = ++ts; nw.st = 1; nw.cut = 1; nw.imp = 0; nw.flg = 0; nw.it = 1;
				pushed = w;
				break;
			}
			else if(nw.dfn < nx.low) nx.low = nw.dfn;
		}
		nx.it = it;
		if(pushed >= 0) { TjStack[top++] = pushed; continue; }
		top--;
		if(top)
		{
			TjNode &np = TjN[TjStack[top-1]];
			if(nx.low < np.low) np.low = nx.low;
			np.st += nx.st;
			if(nx.low >= np.dfn)
			{
				np.flg++;
				if(TjStack[top-1] != rt)
				{
					np.cut += nx.st;
					np.imp += (nx.st*(nx.st-1))/2;
					np.flg = -1000000;          // marks "is cut" for non-root
				}
			}
		}
	}
	TjClock = ts;
	const int nn = ts - base;      // == n
	const int noncut = (nn-1)*(nn-2)/2;
	int *best_v = TjBest;
	int min_impact = INT_MAX;
	best_v[0] = 0;
	for(int i = 1; i <= n; i++)
	{
		TjNode &t = TjN[comp[i]];
		int imp;
		if(t.flg < 0) imp = t.imp + (nn-t.cut)*(nn-t.cut-1)/2;
		else imp = noncut;      // non-cut vertex, or root (original root quirk: same value)
		if(imp < min_impact)
		{
			min_impact = imp;
			best_v[0] = 1;
			best_v[1] = i;
		}
		else if(imp == min_impact)
			best_v[++best_v[0]] = i;
	}
	int choose_v = best_v[rand()%best_v[0]+1];

	if(n > 3)
	{
		TjMemo &me = BiconMemo[hkey & (BICON_MEMO_SIZE-1)];
		if(min_impact >= noncut) { me.key = hkey; me.cnt = 0; }
		else if(best_v[0] <= MEMO_MAXV)
		{
			me.key = hkey; me.cnt = best_v[0];
			for(int a = 0; a < best_v[0]; a++) me.v[a] = comp[best_v[a+1]];
		}
	}
	if(n > 3 && min_impact >= noncut)
	{
		int pick = carve_pick(c);
		if(pick >= 0) return pick;
	}
	return comp[choose_v];
}

int *CompStamp; int CurCompStamp = 0;
int *AddNodeList;
// cached add-back deltas of removed vertices
long *AddDelta; char *DeltaValid; bool AllDirty = true;
long AddBias = 2;	// original: 2 (lambda 0.5)

// Incremental adjacent-component lists of removed vertices (pure speed-up of the add-move evaluation):
// for every removed u, AC lists the components (by stable handle) holding its alive neighbours, with counts.
// Kept exact by remove_node/add_node; rebuilt from scratch whenever ACStale is set (after any bulk construction).
int *CompH, *HIdx, *HFree, HTop = 0, *ACoff, *AClen, *ACh, *ACn; bool ACStale = true;
static inline int h_new(int c) { int h = HFree[--HTop]; CompH[c] = h; HIdx[h] = c; return h; }
static inline void ac_inc(int u,int h)
{
	int *ph = ACh + ACoff[u], *pn = ACn + ACoff[u], l = AClen[u];
	for(int i = 0; i < l; i++) if(ph[i] == h) { pn[i]++; return; }
	ph[l] = h; pn[l] = 1; AClen[u] = l+1;
}
static inline void ac_dec(int u,int h)
{
	int *ph = ACh + ACoff[u], *pn = ACn + ACoff[u], l = AClen[u];
	for(int i = 0; i < l; i++) if(ph[i] == h)
	{
		if(--pn[i] == 0) { ph[i] = ph[l-1]; pn[i] = pn[l-1]; AClen[u] = l-1; }
		return;
	}
}
// vertex x moved from component handle ho to hn: update its removed neighbours
static inline void ac_move(int x,int ho,int hn)
{
	const int *adj = AdjacencyList[x];
	for(int j = 1; j <= adj[0]; j++)
	{
		int y = adj[j];
		if(IndexRemovedV[y] >= 0) { ac_dec(y,ho); ac_inc(y,hn); }
	}
}
static inline void ac_build(int u)
{
	AClen[u] = 0;
	const int *adj = AdjacencyList[u];
	for(int j = 1; j <= adj[0]; j++)
		if(IndexRemovedV[adj[j]] == -1) ac_inc(u,CompH[VInComponent[adj[j]]]);
}
void ac_rebuild()
{
	int N0 = FixedAllocatedSpace/(int)sizeof(int);
	HTop = 0;
	for(int h = N0+1; h >= NbrC; h--) HFree[HTop++] = h;
	for(int c = 0; c < NbrC; c++) { CompH[c] = c; HIdx[c] = c; }
	for(int i = 0; i < NbrRemovedV; i++) ac_build(RemovedV[i]);
	ACStale = false;
}

static inline long compute_add_delta(int u)
{
	long c_size = 0, old_c_size = 0;
	const int *ph = ACh + ACoff[u];
	for(int i = 0, l = AClen[u]; i < l; i++)
	{
		long sz = Components[HIdx[ph[i]]][0];
		c_size += sz;
		old_c_size += sz*(sz-1)/2;
	}
	return c_size*(c_size+AddBias)/2 - old_c_size;
}

static inline long compute_add_delta_scan(int u)
{
	if(++CurCompStamp == INT_MAX)
	{
		for(int j = 0; j < NbrV; j++) CompStamp[j] = 0;
		CurCompStamp = 1;
	}
	long c_size = 0, old_c_size = 0;
	int count = AdjacencyList[u][0],*p2 = &AdjacencyList[u][1];
	for(int j = 1; j <= count; j++, p2++)
		if(IndexRemovedV[*p2] == -1)
		{
			int c1 = VInComponent[*p2];
			if(CompStamp[c1] != CurCompStamp)
			{
				long sz = Components[c1][0];
				c_size += sz;
				old_c_size += sz*(sz-1)/2;
				CompStamp[c1] = CurCompStamp;
			}
		}
	return c_size*(c_size+AddBias)/2 - old_c_size;	// offer S2_v1 variant: exact increase + (AddBias-1)/2*merged size
}

static inline void mark_comp_dirty(int c)
{
	if(AllDirty) return;
	int sz = Components[c][0];
	if(2*sz > K) { AllDirty = true; return; }
	int *p = &Components[c][1];
	for(int k = 0; k < sz; k++, p++)
	{
		int *adj = AdjacencyList[*p];
		for(int j = 1; j <= adj[0]; j++)
			if(IndexRemovedV[adj[j]] >= 0) DeltaValid[adj[j]] = 0;
	}
}

int select_add_node()
{
	int v;
	int *add_node_list = AddNodeList;
	long min_delta = (long)NbrV*NbrV;
	add_node_list[0] = 0;
	bool all = AllDirty;
	AllDirty = false;
	if(ACStale) ac_rebuild();
	for(int i = 0; i < NbrRemovedV; i++)
	{
		int u = RemovedV[i];
		long c_size;
		if(all || !DeltaValid[u])
		{
			c_size = compute_add_delta(u);
			AddDelta[u] = c_size;
			DeltaValid[u] = 1;
		}
		else
			c_size = AddDelta[u];
		if(c_size < min_delta)
		{
			min_delta = c_size;
			add_node_list[0] = 1;
			add_node_list[1] = u;
		}
		else if(c_size == min_delta)
			add_node_list[++add_node_list[0]] = u;
	}

	if(add_node_list[0] == 0)
		v = RemovedV[rand()%NbrRemovedV];
	else
		v = add_node_list[rand()%add_node_list[0]+1];
	return v;
}

void create_a_component(int c,int *mlist,int *list)
{
	AliveDegValid = false;
	int index,*p = &list[1];
	if(Components[c] == NULL)
		Components[c] = new int [NbrV+1];
	Components[c][0] = 0;
	ACStale = true;

	for(int i = 1; i <= list[0]; i++, p++)
	{
		Components[c][++Components[c][0]] = *p;
		IndexVInComponent[*p] = Components[c][0];
		VInComponent[*p] = c;

		index = IndexVInVList[*p];
		mlist[index] = mlist[mlist[0]--];
		IndexVInVList[mlist[index]] = index;
	}

	ObjValue += Components[c][0]*(Components[c][0]-1)/2;
}

void delete_a_component(int c)
{
	if(!ACStale)
	{
		HFree[HTop++] = CompH[c];
		if(c != NbrC-1) { CompH[c] = CompH[NbrC-1]; HIdx[CompH[c]] = c; }
	}
	if(c == --NbrC)
		return;
	Components[c][0] = Components[NbrC][0];
	int *p1 = &Components[c][1];
	int *p2 = &Components[NbrC][1];
	int count = Components[NbrC][0];
	for(int i = 1; i <= count; i++,p1++,p2++)
	{
		*p1 = *p2;
		VInComponent[*p1] = c;
	}
}

// --- incremental component maintenance ---
int *GrpOf;            // group id of a visited vertex (valid when MarkStamp == CurStamp)
int *GrpParent;        // union-find over groups
int *GrpNbr;           // scratch: alive neighbours of the removed vertex
int **GrpVerts;        // per-group vertex list (members) ; size NbrV+1 each lazily
int *GrpSize, *GrpHead, *GrpCap;
int *RootList;

static inline int grp_find(int g)
{
	while(GrpParent[g] != g) { GrpParent[g] = GrpParent[GrpParent[g]]; g = GrpParent[g]; }
	return g;
}

static inline void grp_push(int g,int x)
{
	if(GrpSize[g] == GrpCap[g])
	{
		int nc = GrpCap[g]*2 + 16;
		int *nv = new int[nc];
		if(GrpVerts[g]) { memcpy(nv,GrpVerts[g],sizeof(int)*GrpSize[g]); delete[] GrpVerts[g]; }
		GrpVerts[g] = nv; GrpCap[g] = nc;
	}
	GrpVerts[g][GrpSize[g]++] = x;
}

// move vertex x out of component c (swap-remove) into new component nc
static inline void move_vertex(int x,int c,int nc)
{
	int idx = IndexVInComponent[x];
	int last = Components[c][Components[c][0]--];
	Components[c][idx] = last;
	IndexVInComponent[last] = idx;
	Components[nc][++Components[nc][0]] = x;
	IndexVInComponent[x] = Components[nc][0];
	VInComponent[x] = nc;
	if(!ACStale) ac_move(x,CompH[c],CompH[nc]);
}

void remove_node(int v)
{
	int index = IndexVInComponent[v];
	ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	if(AliveDegValid) { const int *a = AdjacencyList[v]; for(int j = 1; j <= a[0]; j++) AliveDeg[a[j]]--; }

	int c = VInComponent[v];
	ObjValue -= Components[c][0]*(Components[c][0]-1)/2;
	AClen[v] = 0;

	int count = Components[c][0];
	VInComponent[v] = -1;
	DeltaValid[v] = 0;
	{
		int h = ACStale ? -1 : CompH[c];
		int *adj = AdjacencyList[v];
		for(int j = 1; j <= adj[0]; j++)
			if(IndexRemovedV[adj[j]] >= 0) { DeltaValid[adj[j]] = 0; if(h >= 0) ac_dec(adj[j],h); }
	}
	if(--Components[c][0] == 0)
	{
		delete_a_component(c);
		if(!ACStale) AClen[v] = 0;
		return;
	}
	struct ACFin { int v; ~ACFin() { if(!ACStale) ac_build(v); } } ac_fin{v};
	Components[c][index] = Components[c][count];
	IndexVInComponent[Components[c][index]] = index;

	// alive neighbours of v
	int d = 0;
	{
		int *adj = AdjacencyList[v];
		for(int i = 1; i <= adj[0]; i++)
			if(IndexRemovedV[adj[i]] == -1)
				GrpNbr[d++] = adj[i];
	}
	if(d <= 1)
	{
		ObjValue += Components[c][0]*(Components[c][0]-1)/2;
		mark_comp_dirty(c);
		return;
	}

	// interleaved searches from every alive neighbour
	new_stamp();
	int nroots = 0;
	for(int g = 0; g < d; g++)
	{
		int x = GrpNbr[g];
		GrpParent[g] = g;
		GrpSize[g] = 0; GrpHead[g] = 0;
		if(MarkStamp[x] == CurStamp)
		{
			// duplicate neighbour entry: join group
			GrpParent[g] = grp_find(GrpOf[x]);
			continue;
		}
		MarkStamp[x] = CurStamp;
		GrpOf[x] = g;
		grp_push(g,x);
	}
	int active = 0;
	for(int g = 0; g < d; g++)
		if(GrpParent[g] == g) RootList[active++] = g;

	bool split = false;
	while(true)
	{
		// compact root list: keep only roots
		int nr = 0, unfinished = 0;
		for(int i = 0; i < active; i++)
		{
			int g = RootList[i];
			if(GrpParent[g] != g) continue;
			RootList[nr++] = g;
			if(GrpHead[g] < GrpSize[g]) unfinished++;
		}
		active = nr;
		if(active == 1) break;          // everything connected
		if(unfinished <= 1) { split = true; break; }
		for(int i = 0; i < active; i++)
		{
			int g = RootList[i];
			if(GrpParent[g] != g || GrpHead[g] >= GrpSize[g]) continue;
			int x = GrpVerts[g][GrpHead[g]++];
			int *adj = AdjacencyList[x];
			int dx = adj[0];
			for(int j = 1; j <= dx; j++)
			{
				int w = adj[j];
				if(IndexRemovedV[w] != -1) continue;
				if(MarkStamp[w] != CurStamp)
				{
					MarkStamp[w] = CurStamp;
					GrpOf[w] = g;
					grp_push(g,w);
				}
				else
				{
					int h = grp_find(GrpOf[w]);
					if(h != g)
					{
						// merge smaller into larger
						int a = g, b = h;
						if(GrpSize[a] - GrpHead[a] < GrpSize[b] - GrpHead[b]) { a = h; b = g; }
						// append all of b (processed ones get re-scanned harmlessly) -> keep processed order:
						// we append b's unprocessed part, and b's processed part is kept as members only.
						for(int k = GrpHead[b]; k < GrpSize[b]; k++)
							grp_push(a,GrpVerts[b][k]);
						GrpParent[b] = a;
						g = a;
					}
				}
			}
		}
	}

	if(split)
	{
		// finished roots are separate components; the unfinished root (if any) stays in c
		int keep = -1;
		for(int i = 0; i < active; i++)
		{
			int g = RootList[i];
			if(GrpHead[g] < GrpSize[g]) keep = g;
		}
		if(keep == -1)
		{
			// all finished: keep the largest (by member count over all merged groups)
			// compute total membership counts
			long best = -1;
			// count members per root via GrpOf
			for(int i = 0; i < active; i++) GrpHead[RootList[i]] = 0;
			for(int k = 1; k <= Components[c][0]; k++)
				GrpHead[grp_find(GrpOf[Components[c][k]])]++;
			for(int i = 0; i < active; i++)
				if(GrpHead[RootList[i]] > best) { best = GrpHead[RootList[i]]; keep = RootList[i]; }
		}
		// collect vertices of each non-kept root: scan all vertices of groups (members lists of all groups)
		// Each vertex visited belongs to exactly one group's member list (its original group g = GrpOf).
		// Build new components by scanning member lists of all original groups.
		int *newc = GrpNbr; // reuse as map root -> new component id (indexed by root)
		for(int i = 0; i < active; i++)
		{
			int g = RootList[i];
			if(g == keep) continue;
			if(Components[NbrC] == NULL) Components[NbrC] = new int[NbrV+1];
			Components[NbrC][0] = 0;
			if(!ACStale) h_new(NbrC);
			newc[g] = NbrC++;
		}
		// vertices of finished roots: every visited vertex x has GrpOf[x]; iterate over component c
		// (cost bounded by visited set, since unfinished root vertices may be many: iterate visited groups instead)
		for(int g = 0; g < d; g++)
		{
			// original member list of group g holds vertices first pushed into g (index < size), but merges appended
			// copies; use GrpOf to identify the original owner to avoid duplicates
			for(int k = 0; k < GrpSize[g]; k++)
			{
				int x = GrpVerts[g][k];
				if(GrpOf[x] != g) continue;              // copy from a merge
				int r = grp_find(g);
				if(r == keep) continue;
				if(VInComponent[x] != c) continue;       // already moved
				move_vertex(x,c,newc[r]);
			}
		}
		ObjValue += Components[c][0]*(Components[c][0]-1)/2;
		for(int i = 0; i < active; i++)
		{
			int g = RootList[i];
			if(g == keep) continue;
			int nc = newc[g];
			ObjValue += Components[nc][0]*(Components[nc][0]-1)/2;
			mark_comp_dirty(nc);
		}
		mark_comp_dirty(c);
	}
	else
	{
		ObjValue += Components[c][0]*(Components[c][0]-1)/2;
		mark_comp_dirty(c);
	}
}

int *AddComps;
void add_node(int v)
{
	REMOVE(v,RemovedV,IndexRemovedV,NbrRemovedV);
	if(AliveDegValid) { const int *a = AdjacencyList[v]; for(int j = 1; j <= a[0]; j++) AliveDeg[a[j]]++; }
	int count = AdjacencyList[v][0],*p = &AdjacencyList[v][1];

	// distinct neighbouring components
	if(++CurCompStamp == INT_MAX)
	{
		for(int j = 0; j < NbrV; j++) CompStamp[j] = 0;
		CurCompStamp = 1;
	}
	int nc = 0, L = -1, Lsize = -1;
	for(int i = 1; i <= count; i++,p++)
		if(IndexRemovedV[*p] == -1)
		{
			int c1 = VInComponent[*p];
			if(CompStamp[c1] != CurCompStamp)
			{
				CompStamp[c1] = CurCompStamp;
				AddComps[nc++] = c1;
				if(Components[c1][0] > Lsize) { Lsize = Components[c1][0]; L = c1; }
			}
		}

	if(nc == 0)
	{
		if(Components[NbrC] == NULL)
			Components[NbrC] = new int [NbrV+1];
		Components[NbrC][0] = 1;
		Components[NbrC][1] = v;
		IndexVInComponent[v] = 1;
		if(!ACStale)
		{
			int h = h_new(NbrC);
			int *adj = AdjacencyList[v];
			for(int j = 1; j <= adj[0]; j++)
				if(IndexRemovedV[adj[j]] >= 0) ac_inc(adj[j],h);
		}
		VInComponent[v] = NbrC++;
		mark_comp_dirty(NbrC-1);
		return;
	}

	ObjValue -= Components[L][0]*(Components[L][0]-1)/2;
	for(int i = 0; i < nc; i++)
	{
		int c1 = AddComps[i];
		if(c1 == L) continue;
		int s1 = Components[c1][0];
		ObjValue -= s1*(s1-1)/2;
		int *src = &Components[c1][1];
		for(int k = 0; k < s1; k++)
		{
			int x = src[k];
			Components[L][++Components[L][0]] = x;
			IndexVInComponent[x] = Components[L][0];
			VInComponent[x] = L;
			if(!ACStale) ac_move(x,CompH[c1],CompH[L]);
		}
		Components[c1][0] = 0;
	}
	Components[L][++Components[L][0]] = v;
	IndexVInComponent[v] = Components[L][0];
	VInComponent[v] = L;
	ObjValue += Components[L][0]*(Components[L][0]-1)/2;
	if(!ACStale)
	{
		int h = CompH[L];
		int *adj = AdjacencyList[v];
		for(int j = 1; j <= adj[0]; j++)
			if(IndexRemovedV[adj[j]] >= 0) ac_inc(adj[j],h);
	}

	if(nc > 1)
	{
		// delete emptied components in descending index order, tracking L
		// simple insertion sort (nc is small)
		for(int i = 1; i < nc; i++)
		{
			int x = AddComps[i], j = i - 1;
			while(j >= 0 && AddComps[j] < x) { AddComps[j+1] = AddComps[j]; j--; }
			AddComps[j+1] = x;
		}
		for(int i = 0; i < nc; i++)
		{
			int c1 = AddComps[i];
			if(c1 == L) continue;
			int last = NbrC - 1;
			delete_a_component(c1);
			if(L == last) L = c1;
		}
	}
	mark_comp_dirty(L);
}

void read_instance(const char *filename)
{
	ifstream FIC(filename);
    if(!FIC.is_open())
    {
    	cout << "***: Cannot open the file: " << InstanceName << endl;
    	exit(0);
    }

	FIC >> NbrV;
	if(FIC.eof())
	{
		cout << "###: Cannot open the file: " << InstanceName << endl;;
    	exit(-1);
	}

	AdjacencyList = new int *[NbrV];
	Node = new int[NbrV];

	int *temp = new int[NbrV+1];
	NbrE = 0;
	for(int i = 0; i < NbrV; i++)
	{
		int v1,v2;
		FIC >> v1;
		Node[i] = i;

		for(int c = FIC.get(); c != ':' && isspace(c); c = FIC.get());
		bool nextLine = false;

		temp[0] = 0;
		while(!FIC.eof() && !nextLine)
		{
			while(isspace(FIC.peek()))
				nextLine = (FIC.get()=='\n');

			if(!nextLine)
			{
				FIC >> v2;
				temp[++temp[0]] = v2;
				NbrE++;
			}
		}

		// adjacency node list
		AdjacencyList[v1] = new int [temp[0]+1];
		for(int i = 0; i <= temp[0]; i++)
		{
			AdjacencyList[v1][i] = temp[i];
		}
	}
    FIC.close();

	NbrE /= 2;
	delete temp;
}

void read_large_instance(const char *filename)
{
	ifstream FIC(filename);
    if(!FIC.is_open())
    {
    	cout << "***: Cannot open the file: " << InstanceName << endl;
    	exit(0);
    }

    int rows,colomns;
	FIC >> rows >> colomns >> NbrE;
	NbrV = rows > colomns ? rows : colomns;
	if(FIC.eof())
	{
		cout << "###: Cannot open the file: " << InstanceName << endl;;
    	exit(-1);
	}

	AdjacencyList = new int *[NbrV];
	for(int i = 0; i < NbrV; i++)
		AdjacencyList[i] = new int[NbrV+1];
	Node = new int[NbrV];
	for(int i = 0; i < NbrV; i++)
		AdjacencyList[i][0] = 0;

	int v1,v2,temp1,temp2;
	double temp3;
	for(int i = 0; i < NbrV; i++)
	{
		FIC >> temp1 >> temp2 >> temp3;
		if(temp1 == temp2)
			continue;
		v1 = temp1 - 1;
		v2 = temp2 - 1;
		Node[i] = i;

		// adjacency node list
		AdjacencyList[v1][++AdjacencyList[v1][0]] = v2;
		AdjacencyList[v2][++AdjacencyList[v2][0]] = v1;
	}
    FIC.close();
}

void setup_data()
{
	{
		double m1 = 0, m2 = 0;
		for(int i = 0; i < NbrV; i++) { double d = AdjacencyList[i][0]; m1 += d; m2 += d*d; }
		m1 /= NbrV; m2 /= NbrV;
		double cv2 = m1 > 0 ? m2/(m1*m1) - 1.0 : 0.0;
		DegP = 0.5*std::min(1.0, 4.0*cv2);
	}
	FixedAllocatedSpace = NbrV*sizeof(int);
	NTotalV = NbrV; AliveDeg = new int[NbrV]; AliveDegValid = false;
	Components = new int * [NbrV];
	for(int i = 0; i < NbrV; i++)
		Components[i] = new int[NbrV+1];

	VInComponent = new int [NbrV];
	IndexVInComponent = new int [NbrV];
	LargeComponentList = new int [NbrV];
	List = new int [NbrV+1];
	VList = new int [NbrV+1];
	IndexVInVList = new int [NbrV];
	RemovedV = new int [NbrV];
	IndexRemovedV = new int [NbrV];
	ImprovedRemovedV = new int[NbrV];
	BestRemovedV = new int [NbrV];
	UsedV = new int[NbrV];
	IsMarked = new bool [NbrV];
	VAge = new int[NbrV];
	ReducedV = new int[NbrV];
	PoolV = new int[NbrV];
	ParentMask = new char[NbrV](); RegStamp = new int[NbrV](); RegQueue = new int[NbrV+1];
	RegCell = new int[NbrV]; CellSide = new int[NbrV+1];
	MarkStamp = new int[NbrV](); DfsStack = new int[NbrV+1];
	CompStamp = new int[NbrV](); AddNodeList = new int[NbrV+1]; AddComps = new int[NbrV+1];
	CandBuf = new int[NbrV+1];
	TjN = new TjNode[NbrV](); TjStack = new int[NbrV+1]; TjBest = new int[NbrV+1];
	{
		// contiguous adjacency storage
		long tot = 0;
		for(int i = 0; i < NbrV; i++) tot += AdjacencyList[i][0] + 1;
		int *block = new int[tot];
		long pos = 0;
		for(int i = 0; i < NbrV; i++)
		{
			int d = AdjacencyList[i][0];
			memcpy(block+pos,AdjacencyList[i],sizeof(int)*(d+1));
			delete[] AdjacencyList[i];
			AdjacencyList[i] = block+pos;
			pos += d+1;
		}
	}
	AddDelta = new long[NbrV]; DeltaValid = new char[NbrV]();
	{
		CompH = new int[NbrV+2]; HIdx = new int[NbrV+2]; HFree = new int[NbrV+2];
		ACoff = new int[NbrV]; AClen = new int[NbrV]();
		long tot = 0;
		for(int i = 0; i < NbrV; i++) { ACoff[i] = (int)tot; tot += AdjacencyList[i][0]; }
		ACh = new int[tot+1]; ACn = new int[tot+1];
	}
	{
		int maxd = 1;
		for(int i = 0; i < NbrV; i++) if(AdjacencyList[i][0] > maxd) maxd = AdjacencyList[i][0];
		GrpOf = new int[NbrV]; GrpParent = new int[maxd+1]; GrpNbr = new int[maxd+1];
		GrpVerts = new int*[maxd+1](); GrpSize = new int[maxd+1]; GrpHead = new int[maxd+1];
		GrpCap = new int[maxd+2](); RootList = new int[maxd+1];
	}

	// Population
	Pop = new int*[PS+1];
	for(int i = 0; i < PS+1; i++)
		Pop[i] = new int[NbrV];
	PopCost = new double[PS+1];
	SolSimilarity = new double*[PS+1];
	for(int i = 0; i < PS+1; i++)
		SolSimilarity[i] = new double[PS+1];
	PopSimilarity = new double[PS+1];
	PopScore = new double[PS+1];
}

void clear_data()
{
	for(int i = 0; i < NbrV; i++)
		delete Components[i];

	delete[] VInComponent;
	delete[] IndexVInComponent;
	delete[] LargeComponentList;
	delete[] List;
	delete[] VList;
	delete[] IndexVInVList;
	delete[] RemovedV;
	delete[] IndexRemovedV;
	delete[] ImprovedRemovedV;
	delete[] BestRemovedV;
	delete[] UsedV;
	delete[] IsMarked;
	delete[] VAge;
	delete[] ReducedV;

	// population
	delete[] PopCost;
	delete[] PopSimilarity;
	delete[] PopScore;
	for(int i = 0; i < PS+1; i++)
	{
		delete Pop[i];
		delete SolSimilarity[i];
	}
}

void update_improved_sol()
{
	ImprovedTime = (clock() - StartTime)/CLOCKS_PER_SEC;;
	ImprovedObjValue = ObjValue;
	ImprovedNbrC = NbrC;
	NbrImprovedRemovedV = NbrRemovedV;
	for(int i = 0; i < NbrRemovedV; i++)
		ImprovedRemovedV[i] = RemovedV[i];
}

void update_best_sol()
{
	BestTime = ImprovedTime;
	BestObjValue = ImprovedObjValue;
	BestNbrC = ImprovedNbrC;
	NbrBestRemovedV = NbrImprovedRemovedV;
	for(int i = 0; i < NbrImprovedRemovedV; i++)
		BestRemovedV[i] = ImprovedRemovedV[i];
}

// construct a random solution
void random_construct_sol()
{
	int v;
	int index;
	int *candidate_v;
	candidate_v = new int[NbrV];
	int nbr_candidate_v = 0;

	for(int i = 0; i < NbrV; i++)
	{
		candidate_v[nbr_candidate_v] = Node[i];
		nbr_candidate_v++;
	}
	memset(UsedV,0,FixedAllocatedSpace);

	NbrRemovedV = 0;
	while(NbrRemovedV < K)
	{
		srand(cnp_clock());
		index = rand()%nbr_candidate_v;
		v = candidate_v[index];
		UsedV[v] = 1;

		nbr_candidate_v--;
		candidate_v[index] = candidate_v[nbr_candidate_v];

		VInComponent[v] = -1;
		IndexVInComponent[v] = -1;
		ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	}

	int count = 0;
	for(int i = 0; i < NbrV; i++)
		if(UsedV[Node[i]] == 0)
		{
			VInComponent[Node[i]] = -1;
			IndexVInComponent[Node[i]] = -1;
			IndexRemovedV[Node[i]] = -1;
			count++;
			VList[count] = Node[i];
			IndexVInVList[Node[i]] = count;
		}
	VList[0] = NbrV - K;

	NbrC = 0;
	ObjValue = 0;
	while(VList[0])
	{
		depth_first_search(VList[1],List);
		create_a_component(NbrC,VList,List);
		NbrC++;
	}
	delete[] candidate_v;
}

// uniform-crossover start for the reduced instance (offer S1_v1)
void inherited_construct_sol()
{
	memset(UsedV,0,FixedAllocatedSpace);
	NbrRemovedV = 0;
	// scale of the parents' components (as for the geographic start below): q = min(1/2, 20 s/n)
	double qut = 0;
	{
		int ntot = NbrV + NbrReducedV;
		int kept = ntot - (K + NbrReducedV); if(kept < 1) kept = 1;
		qut = 20.0*(1.0 + 2.0*ParentCostAvg/kept)/ntot;
		if(qut > 0.5) qut = 0.5;
	}
	if(NbrPoolV > K && (double)rand()/RAND_MAX < qut)
	{
		// with probability q (solutions made of few large components, where whole separators matter):
		// union-trim crossover start: remove the union of the parents' free removed vertices (over budget,
		// both parents' separators at once), then greedily re-insert the vertex whose return increases the
		// connectivity least (same add rule as the LS) until exactly K remain
		for(int i = 0; i < NbrPoolV; i++)
		{
			int v = PoolV[i];
			UsedV[v] = 1;
			VInComponent[v] = -1;
			IndexVInComponent[v] = -1;
			ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
		}
		int count = 0;
		for(int i = 0; i < NbrV; i++)
			if(UsedV[Node[i]] == 0)
			{
				VInComponent[Node[i]] = -1;
				IndexVInComponent[Node[i]] = -1;
				IndexRemovedV[Node[i]] = -1;
				count++;
				VList[count] = Node[i];
				IndexVInVList[Node[i]] = count;
			}
		VList[0] = count;
		NbrC = 0;
		ObjValue = 0;
		while(VList[0])
		{
			depth_first_search(VList[1],List);
			create_a_component(NbrC,VList,List);
			NbrC++;
		}
		AllDirty = true;
		while(NbrRemovedV > K)
			add_node(select_add_node());
		AllDirty = true;
		return;
	}
	int nbr = NbrPoolV;
	// geographic start with probability q = min(1, 20 s/n) (s/n = share of the graph held by a typical
	// component): solutions made of many small components (separable local choices) keep the uniform draw
	double q = 0;
	if(NbrPoolV > 0)
	{
		int ntot = NbrV + NbrReducedV;
		int kept = ntot - (K + NbrReducedV); if(kept < 1) kept = 1;
		q = 20.0*(1.0 + 2.0*ParentCostAvg/kept)/ntot;
	}
	if(q > GEO_QMAX) q = GEO_QMAX;
	if(NbrPoolV > 0 && (double)rand()/RAND_MAX < q)
	{
		// geographic crossover on the scale of the solutions' components: the whole graph is cut into
		// Voronoi cells (simultaneous BFS from random seeds) of size s, s = vertex-weighted mean
		// component size of the parents = sum|C|^2/sum|C| ~ 1 + 2 cost/(n-K); each cell takes the
		// removed vertices of parent A or of parent B (coin flip). Small components (sparse graphs):
		// many small cells ~ uniform crossover; a few huge components (dense graphs): a few large
		// coherent regions, so each parent's separators are kept whole.
		int ntot = NbrV + NbrReducedV;
		int kept = ntot - (K + NbrReducedV); if(kept < 1) kept = 1;
		double csz = 1.0 + 2.0*ParentCostAvg/kept;	// typical component size s
		int m = (int)(ntot/csz + 0.5);
		if(m < 2) m = 2;
		if(m > ntot) m = ntot;
		if(++CurRegStamp == INT_MAX) { for(int i = 0; i < ntot; i++) RegStamp[i] = 0; CurRegStamp = 1; }
		int head = 0, tail = 0;
		bool sa = false, sb = false;
		for(int c = 0; c < m; c++)
		{
			CellSide[c] = (rand()&1) ? 1 : 2;
			if(CellSide[c] == 1) sa = true; else sb = true;
		}
		if(!sa) CellSide[rand()%m] = 1;
		else if(!sb) CellSide[rand()%m] = 2;
		for(int c = 0; c < m; c++)
		{
			int x = rand()%ntot, tries = 0;
			while(RegStamp[x] == CurRegStamp && tries++ < 20) x = rand()%ntot;
			if(RegStamp[x] == CurRegStamp) continue;
			RegStamp[x] = CurRegStamp; RegCell[x] = c; RegQueue[tail++] = x;
		}
		while(head < tail)
		{
			int x = RegQueue[head++];
			int cx = RegCell[x];
			const int *adj = AdjacencyList[x];
			for(int j = 1; j <= adj[0]; j++)
			{
				int w = adj[j];
				if(RegStamp[w] != CurRegStamp) { RegStamp[w] = CurRegStamp; RegCell[w] = cx; RegQueue[tail++] = w; }
			}
		}
		// partition the pool: chosen (front) / others (back)
		int nch = 0;
		for(int i = 0; i < NbrPoolV; i++)
		{
			int v = PoolV[i];
			UsedV[v] = 0;
			int side = (RegStamp[v] == CurRegStamp) ? CellSide[RegCell[v]] : 2;
			if(ParentMask[v] & side) { PoolV[i] = PoolV[nch]; PoolV[nch++] = v; }
		}
		// take chosen ones first (random order if too many), then other pool vertices
		while(NbrRemovedV < K && nch > 0)
		{
			int index = rand()%nch;
			int v = PoolV[index];
			PoolV[index] = PoolV[--nch];
			PoolV[nch] = v;
			// move v out of the [0,nbr) range
			--nbr; int t = PoolV[nbr]; PoolV[nbr] = v; PoolV[nch] = t;
			UsedV[v] = 1;
			VInComponent[v] = -1;
			IndexVInComponent[v] = -1;
			ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
		}
		// remaining range [0,nbr) holds the not-yet-taken pool vertices (nch chosen unused, then others)
	}
	while(NbrRemovedV < K && nbr > 0)
	{
		int index = rand()%nbr;
		int v = PoolV[index];
		PoolV[index] = PoolV[--nbr];
		PoolV[nbr] = v;
		UsedV[v] = 1;
		VInComponent[v] = -1;
		IndexVInComponent[v] = -1;
		ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	}
	while(NbrRemovedV < K)
	{
		int v = Node[rand()%NbrV];
		if(UsedV[v]) continue;
		UsedV[v] = 1;
		VInComponent[v] = -1;
		IndexVInComponent[v] = -1;
		ADD(v,RemovedV,IndexRemovedV,NbrRemovedV);
	}
	int count = 0;
	for(int i = 0; i < NbrV; i++)
		if(UsedV[Node[i]] == 0)
		{
			VInComponent[Node[i]] = -1;
			IndexVInComponent[Node[i]] = -1;
			IndexRemovedV[Node[i]] = -1;
			count++;
			VList[count] = Node[i];
			IndexVInVList[Node[i]] = count;
		}
	VList[0] = NbrV - K;
	NbrC = 0;
	ObjValue = 0;
	while(VList[0])
	{
		depth_first_search(VList[1],List);
		create_a_component(NbrC,VList,List);
		NbrC++;
	}
}

/* two-stages neighborhood search procedure */
void CBNS_procedure()
{
	long nbr_step = 0;
	long nbr_idle_steps = 0;
	int c,v;
	for(int i = 0; i < NbrV; i++)
		VAge[Node[i]] = 0;

	ImprovedObjValue = INT_MAX;
	AllDirty = true; ACStale = true;
	while(nbr_idle_steps < MAX_IDLE_STEPS)
	{
		nbr_step++;
		// Remove a node from G
		c = select_remove_component();	// select a larger component
		v = select_remove_node_with_weight(c);	// randomly remove a node from selected component
		remove_node(v);
		VAge[v] = nbr_step;

		// Add a node back to G
		v = select_add_node();
		add_node(v);	//  add a node to G which gives the minimum increase in f
		VAge[v] = nbr_step;

		// Update the best solution
		if(ObjValue < ImprovedObjValue)
		{
			update_improved_sol();
			if(ImprovedObjValue == BKV && OF == true)
				break;
			nbr_idle_steps = 0;
		}
		else
			nbr_idle_steps++;

		if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
			break;
	}
}

/* Separator bisection move: BFS level structure of the largest component from a pseudo-peripheral
   vertex; the thinned level set (level-l vertices with a neighbour on level l+1) is a vertex separator.
   Remove the level that best bisects the component net of the estimated cost of re-adding as many
   vertices, add back greedily, keep if the objective does not worsen, otherwise revert. */
#include <vector>
#include <algorithm>
static std::vector<int> SepLvl, SepStamp, SepQ, SepCnt, SepThin, SepS, SepAdded;
static std::vector<long> SepD;
static int SepCur = 0;
#define SEP_PROB 0.02
static int sep_bfs(int src)
{
	if(++SepCur == INT_MAX) { std::fill(SepStamp.begin(), SepStamp.end(), 0); SepCur = 1; }
	int h = 0, t = 0;
	SepQ[t++] = src; SepStamp[src] = SepCur; SepLvl[src] = 0;
	while(h < t)
	{
		int x = SepQ[h++];
		int *adj = AdjacencyList[x];
		for(int j = 1; j <= adj[0]; j++)
		{
			int w = adj[j];
			if(IndexRemovedV[w] == -1 && SepStamp[w] != SepCur)
			{
				SepStamp[w] = SepCur; SepLvl[w] = SepLvl[x] + 1; SepQ[t++] = w;
			}
		}
	}
	return t;
}
bool separator_move(long step)
{
	int N0 = FixedAllocatedSpace/(int)sizeof(int);
	if((int)SepLvl.size() < N0)
	{
		SepLvl.assign(N0,0); SepStamp.assign(N0,0); SepQ.assign(N0,0); SepCnt.assign(N0+2,0);
		SepThin.assign(N0+2,0); SepS.reserve(N0); SepAdded.reserve(N0); SepD.reserve(N0);
	}
	if(NbrRemovedV == 0) return false;
	int c = 0;
	for(int i = 1; i < NbrC; i++) if(Components[i][0] > Components[c][0]) c = i;
	long sz = Components[c][0];
	if(sz < 8) return false;
	int t = sep_bfs(Components[c][1 + rand()%sz]);
	int u = SepQ[t-1];
	t = sep_bfs(u);
	int d = SepLvl[SepQ[t-1]];
	if(d < 2) return false;
	for(int l = 0; l <= d; l++) { SepCnt[l] = 0; SepThin[l] = 0; }
	for(int i = 0; i < t; i++)
	{
		int x = SepQ[i], l = SepLvl[x];
		SepCnt[l]++;
		int *adj = AdjacencyList[x];
		for(int j = 1; j <= adj[0]; j++)
		{
			int w = adj[j];
			if(IndexRemovedV[w] == -1 && SepLvl[w] == l+1) { SepThin[l]++; break; }
		}
	}
	// sorted current add deltas (re-add cost estimate)
	SepD.clear();
	if(ACStale) ac_rebuild();
	for(int i = 0; i < NbrRemovedV; i++)
	{
		int r = RemovedV[i];
		if(AllDirty || !DeltaValid[r]) { AddDelta[r] = compute_add_delta(r); DeltaValid[r] = 1; }
		SepD.push_back(AddDelta[r]);
	}
	AllDirty = false;
	int smax = 0;
	for(int l = 1; l < d; l++) if(SepThin[l] > smax) smax = SepThin[l];
	if(smax > NbrRemovedV) smax = NbrRemovedV;
	if(smax <= 0) return false;
	std::partial_sort(SepD.begin(), SepD.begin()+smax, SepD.end());
	for(int k = 1; k < smax; k++) SepD[k] += SepD[k-1];	// prefix sums
	long below = SepCnt[0], best_net = 0; int best_l = -1;
	long whole = sz*(sz-1)/2;
	for(int l = 1; l < d; l++)
	{
		long s = SepThin[l];
		long a = below + (SepCnt[l] - s), b = sz - a - s;
		below += SepCnt[l];
		if(s <= 0 || s > smax) continue;
		long net = whole - a*(a-1)/2 - b*(b-1)/2 - SepD[s-1];
		if(net > best_net) { best_net = net; best_l = l; }
	}
	if(best_l < 0) return false;
	SepS.clear();
	for(int i = 0; i < t; i++)
	{
		int x = SepQ[i];
		if(SepLvl[x] != best_l) continue;
		int *adj = AdjacencyList[x];
		for(int j = 1; j <= adj[0]; j++)
		{
			int w = adj[j];
			if(IndexRemovedV[w] == -1 && SepLvl[w] == best_l+1 && SepStamp[w] == SepCur) { SepS.push_back(x); break; }
		}
	}
	int old = ObjValue;
	for(int x : SepS) remove_node(x);
	SepAdded.clear();
	for(size_t k = 0; k < SepS.size(); k++)
	{
		int v = select_add_node();
		add_node(v);
		SepAdded.push_back(v);
	}
	if(ObjValue > old)
	{
		for(int k = (int)SepAdded.size()-1; k >= 0; k--) remove_node(SepAdded[k]);
		for(int k = (int)SepS.size()-1; k >= 0; k--) add_node(SepS[k]);
		return false;
	}
	for(int x : SepS) VAge[x] = step;
	for(int x : SepAdded) VAge[x] = step;
	return true;
}


void CHNS_procedure()
{
	long nbr_step = 0;
	long nbr_idle_steps = 0;
	int c,v;
	for(int i = 0; i < NbrV; i++)
		VAge[Node[i]] = 0;

	ImprovedObjValue = INT_MAX;
	AllDirty = true; ACStale = true;
	while(nbr_idle_steps < MAX_IDLE_STEPS)
	{
		nbr_step++;
		if((double)rand()/RAND_MAX < SEP_PROB && separator_move(nbr_step)) goto sep_done;	// offer S2_v5
		{
		// strategic oscillation (offer S1_v6): occasionally a depth-d compound move (d removals, then d best add-backs)
		int depth = 1;
		if(rand() < (int)(OSC_P*RAND_MAX)) depth = 2 + rand()%(OSC_DMAX-1);
		if(depth > NbrV - NbrRemovedV - 1) depth = 1;
		for(int d = 0; d < depth; d++)
		{
		// Remove a node from G
		c = select_remove_component();	// select a larger component
	    double ns = (double)rand()/RAND_MAX;
		if(ns < THETA)
		    v = select_remove_node_with_impact(c);
		else if(ns < THETA + DegP*(1.0-THETA))
		    v = select_remove_node_by_degree(c);
		else
		    v = select_remove_node_with_weight(c);	// randomly remove a node from selected component
		remove_node(v);
		VAge[v] = nbr_step;
		}
		for(int d = 0; d < depth; d++)
		{
		// Add a node back to G
		v = select_add_node();
		add_node(v);	//  add a node to G which gives the minimum increase in f
		VAge[v] = nbr_step;
		}
		}
		sep_done:

		// Update the best solution
		if(ObjValue < ImprovedObjValue)
		{
			update_improved_sol();
			if(ImprovedObjValue == BKV && OF == true)
			//if(ImprovedObjValue <= TTTObjValue)
				break;
			nbr_idle_steps = 0;
		}
		else
			nbr_idle_steps++;

		if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
			break;
	}
}

/* Population initialization procedure */
void build_population()
{
	int swap_out_v,swap_in_v;
	int nbr_sol = 0;
	int true_nbr_sol = 0;
	while(nbr_sol < PS)
	{
		srand(cnp_clock());
		true_nbr_sol++;

		// generate an initial solution
		random_construct_sol();
		update_improved_sol();

		// improve it by a neighborhood search procedure
		CBNS_procedure();
		ascend_sort(ImprovedRemovedV);

    	// update the best solution
    	if(ImprovedObjValue < BestObjValue)
    	{
    		update_best_sol();
        	if(BestObjValue == BKV && OF == true)
        		break;
    	}

    	// check the time limit
    	if((clock()-StartTime)/CLOCKS_PER_SEC >= LimitTime)
    		return;

		// modify the improved solution
		int is_update = 1;
		int count = 0;
		int flag;
		while(is_duplicate_sol(nbr_sol) == true)
        {
			if(is_update == 1)
			{
				memset(UsedV,0,FixedAllocatedSpace);
				for(int i = 0; i < K; i++)
					UsedV[ImprovedRemovedV[i]] = 1;

				NbrRemovedV = 0;
				for(int i = 0; i < NbrV; i++)
					if(UsedV[Node[i]] == 1)
					{
						VInComponent[Node[i]] = -1;
						IndexVInComponent[Node[i]] = -1;
						ADD(Node[i],RemovedV,IndexRemovedV,NbrRemovedV);
					}
					else
					{
						VInComponent[Node[i]] = -1;
						IndexVInComponent[Node[i]] = -1;
						IndexRemovedV[Node[i]] = -1;
						count++;
						VList[count] = Node[i];
						IndexVInVList[Node[i]] = count;
					}
				VList[0] = NbrV - NbrRemovedV;
				NbrC = 0;
				ObjValue = 0;
				while(VList[0])
				{
					depth_first_search(VList[1],List);
					create_a_component(NbrC,VList,List);
					NbrC++;
				}
				is_update = 0;
			}

			// add a vertex back to G
			AllDirty = true; ACStale = true;
			swap_out_v = select_add_node();
			add_node(swap_out_v);

			// remove a vertex from G
			flag = 0;
			while(flag == 0)
			{
				swap_in_v = Node[rand()%NbrV];
				if(VInComponent[swap_in_v] != -1)
					break;
			}
			remove_node(swap_in_v);

			ascend_sort(ImprovedRemovedV);
			update_improved_sol();
        }

    	// insert it into the population
    	PopCost[nbr_sol] = ImprovedObjValue;
    	for(int i = 0; i < K; i++)
    		Pop[nbr_sol][i] = ImprovedRemovedV[i];
    	nbr_sol++;
	}

	// evaluate all individuals in the population
    for(int i = 0; i < PS; i++)
    {
    	for(int j = i + 1; j < PS; j++)
    	{
    		SolSimilarity[i][j] = compute_SolSimilarity(i,j);
    		SolSimilarity[j][i] = SolSimilarity[i][j];
    	}
    	SolSimilarity[i][i] = 1.0;
    }
}

/* update the pool */
bool update_population()
{
	bool is_updated = false;
	// insert the offspring solution into the population
	PopCost[PS] = ImprovedObjValue;
	for(int i = 0; i < K; i++)
		Pop[PS][i] = ImprovedRemovedV[i];

    for(int i = 0; i < PS+1; i++)
    {
    	SolSimilarity[i][PS] = compute_SolSimilarity(i,PS);
    	SolSimilarity[PS][i] = SolSimilarity[i][PS];
    }
    SolSimilarity[PS][PS] = 1.0;

    // Calculate the average distance of each individual with the whole population
    for(int i = 0; i < PS+1; i++)
    {
    	PopSimilarity[i] = 0.0;
    	for(int j = 0; j < PS+1; j++)
    		if(j != i)
    			PopSimilarity[i] += SolSimilarity[i][j];

    	PopSimilarity[i] = PopSimilarity[i]/PS;
    }

    int *cost_rank,*distance_rank;
    cost_rank = new int[PS+1];
    distance_rank = new int[PS+1];

    for(int i = 0; i < PS+1; i++)
    {
    	cost_rank[i] = i + 1;
    	distance_rank[i] = i + 1;
    }

    calculate_its_rank(1,PS+1,PopCost,cost_rank);
    calculate_its_rank(1,PS+1,PopSimilarity,distance_rank);

    // Compute the score of each individual in the population
    for(int i = 0; i < PS+1; i++)
    	PopScore[i] = ALPHA*((double) cost_rank[i]) + (1.0-ALPHA)*((double) distance_rank[i]);

    // find out the worst solution
    double min_score = (double)INT_MAX;
    int index_worst_sol;
    for(int i = 0; i < PS+1; i++)
    	if(PopScore[i] < min_score)
    	{
    		min_score = PopScore[i];
    		index_worst_sol = i;
    	}

	// replace the worst solution if condition is met.
    if(index_worst_sol != PS && is_duplicate_sol(PS) == false)
    {
    	is_updated = true;

    	//update pop
    	PopCost[index_worst_sol] = PopCost[PS];
        for(int i = 0; i < K; i++)
        	Pop[index_worst_sol][i] = Pop[PS][i];

        // update sol_distance
        for(int i = 0; i < PS; i++)
        	if(i != index_worst_sol)
        	{
        		SolSimilarity[i][index_worst_sol] = SolSimilarity[PS][i];
        		SolSimilarity[index_worst_sol][i] = SolSimilarity[PS][i];
        	}
        	else
        		SolSimilarity[index_worst_sol][index_worst_sol] = 1.0;
     }
    delete[] cost_rank;
    delete[] distance_rank;
    return is_updated;
}

void pattern_guided_instance_reduction()
{
	ACStale = true;
	int ID1, ID2;
	// randomly select two solutions
    ID1 = rand()%PS;
    while(1)
    {
    	ID2 = rand()%PS;
    	if(ID2 != ID1)
    	    break;
    }
	memset(UsedV,0,FixedAllocatedSpace);
	// find the common nodes
    for(int i = 0; i < NbrV; i++) ParentMask[i] = 0;
    for(int i = 0; i < K; i++)
    {
    	UsedV[Pop[ID1][i]]++;
    	UsedV[Pop[ID2][i]]++;
    	ParentMask[Pop[ID1][i]] |= 1;
    	ParentMask[Pop[ID2][i]] |= 2;
    }
    ParentCostAvg = 0.5*(PopCost[ID1] + PopCost[ID2]);

	int NodeNum = 0;
	NbrReducedV = 0;
	NbrPoolV = 0;
	// reduce an instance based on sharing nodes
	for(int i = 0; i < NbrV; i++)
	{
		double r = (double)rand()/RAND_MAX;
		if(UsedV[Node[i]] == 2 && r < BETA)
		{
		    ReducedV[NbrReducedV++] = Node[i];
		    VInComponent[Node[i]] = -2;
		    IndexVInComponent[Node[i]] = -2;
		    IndexRemovedV[Node[i]] = -2;
		}
		else
		{
			if(UsedV[Node[i]] >= 1) PoolV[NbrPoolV++] = Node[i];
			Node[NodeNum++] = Node[i];
		}
	}

	K = K - NbrReducedV;
	NbrV = NbrV - NbrReducedV;
}

void expand_solution()
{
	ACStale = true;
	K = K + NbrReducedV;
	NbrV = NbrV + NbrReducedV;
	for(int i = 0; i < NbrReducedV; i++)
	{
		ADD(ReducedV[i],RemovedV,IndexRemovedV,NbrRemovedV);
	    VInComponent[ReducedV[i]] = -1;
	    IndexVInComponent[ReducedV[i]] = -1;
	}
	update_improved_sol();

	for(int i = 0; i < NbrV; i++)
		Node[i] = i;
}

void pattern_guided_solution_construction()
{
	int c, v;
	int ID1, ID2;
	// randomly select two solutions
    ID1 = rand()%PS;
    while(1)
    {
    	ID2 = rand()%PS;
    	if(ID2 != ID1)
    	    break;
    }
	memset(UsedV,0,FixedAllocatedSpace);
	// find the common nodes
    for(int i = 0; i < K; i++)
    {
    	UsedV[Pop[ID1][i]]++;
    	UsedV[Pop[ID2][i]]++;
    }

	// generate an offspring by crossover
    int count = 0;
    NbrRemovedV = 0;
    double r;
	for(int i = 0; i < NbrV; i++)
	{
		r = (double)rand()/RAND_MAX;
		if(UsedV[i] == 2 && r < BETA)
		{
			VInComponent[i] = -1;
			IndexVInComponent[i] = -1;
			ADD(i,RemovedV,IndexRemovedV,NbrRemovedV);
		}
		else
		{
			VInComponent[i] = -1;
			IndexVInComponent[i] = -1;
			IndexRemovedV[i] = -1;
			count++;
			VList[count] = i;
			IndexVInVList[i] = count;
		}
	}
    VList[0] = NbrV - NbrRemovedV;

    NbrC = 0;
	ObjValue = 0;
	while(VList[0])
	{
		depth_first_search(VList[1],List);
		create_a_component(NbrC,VList,List);
		NbrC++;
	}

    while(NbrRemovedV < K)
    {
		// Remove a node from G
		c = select_remove_component();	// select a larger component
		v = select_remove_node_at_random(c); // randomly remove a node from selected component
		remove_node(v);
    }
}

void reduce_solve_combine()
{
	// offer S2_v1 variant: per-generation add-bias portfolio (lambda 0.5 or 8)
	AddBias = (rand()&1) ? 17 : 2;
	AllDirty = true; ACStale = true;
	// Step1. reduce instance based on common pattern
	pattern_guided_instance_reduction();

	// Step2. solve the reduced instance by a local search
	inherited_construct_sol();
	update_improved_sol();
	CHNS_procedure();

	// Step3. expand the solution for the original instance
	expand_solution();
	// update the best solution
	if(ImprovedObjValue < BestObjValue)
	{
		ascend_sort(ImprovedRemovedV);
		update_best_sol();
    	if(BestObjValue == BKV && OF == true)
    		return;
	}
}

void Instance_Reduction_Based_Search_CNP()
{
	int nbr_gens, nbr_idle_gens;
	StartTime = clock();
	BestObjValue = INT_MAX;
	nbr_gens = 0;
	nbr_idle_gens = 0;

	/* Step1. Population initialization */
	build_population();
    if(BestObjValue == BKV && OF == true) // terminate if a new upper limit or an optima is found
	    return;

	//Population Evolution
	while((clock()-StartTime)/CLOCKS_PER_SEC < LimitTime)
	{
		/* Step2. Reduce instance and resolve the instance */
		reduce_solve_combine();
	    if(BestObjValue == BKV && OF == true) // terminate if a new upper limit is found
	        return;

		/* Step3. Search around the expanded solution */
	    CHNS_procedure();
	    ascend_sort(ImprovedRemovedV);
	    nbr_gens++;

        /* Record the best solution */
	    if(ImprovedObjValue < BestObjValue)
	    {
	        update_best_sol();
	        BestNbrGens = nbr_gens;
	        if(BestObjValue == BKV && OF == true) // terminate if a new upper limit is found
	            return;
	        nbr_idle_gens = 0;
	    }
    	else
    		nbr_idle_gens++;

	    /* Step4. Update Population */
	    update_population();
	}
}
