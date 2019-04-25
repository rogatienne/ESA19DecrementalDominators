/*---------------------------------------------------------------
| Dynamic Dominators - Depth Based Search algorithm
| uses SNCA for batch processing
*---------------------------------------------------------------*/

#ifdef _WIN32
	#include <chrono>
#elif _linux
	#include "rfw_timer.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <cmath>
#include <limits.h>

using namespace std;

#define MAXLINE       100   /* max length of input line */
#define INPUT_a 0
#define INPUT_i 1
#define INPUT_d 2 
#define INPUT_e 3
#define T 1.4

#define UPDATE_LOW_HIGH 1 // 0 -> updates LowHigh, 1 -> dynamic algo

struct representative{
	int representativesName;
	int leaves;
	unsigned long long int tag;

	struct node* nodesListHead;
	struct node* nodesListTail;
	struct representative* leftRepresentative;
	struct representative* rightRepresentative;
};

struct node{
	int nodesName;
	unsigned long long int tag;

	struct node* leftNode;
	struct node* rightNode;
	struct representative* rep;
};

struct node** nodesTablePreorder;
struct node** nodesTablePostorder;
struct representative* representativesListHeadPreorder;
struct representative* representativesListTailPostorder;
int representativesCounterPreorder;
int representativesCounterPostorder;
int nodesPerRepresentative;
unsigned long long int tagSize;

char line[MAXLINE]; /* stores input line */
int *input_file; // stores input arcs
int r; // source
int n, m; /* number of nodes, arcs */
int *buffer;

// input graph representation
// dynamic adjacency lists for forward and reverse graphneighbour
int *First;         // position of first out-neighbor
int *Target;        // stores out-neighbors
int *Next;          // position of next out-neighbor
int *r_First;       // position of first in-neighbor
int *r_Target;      // stores in-neighbors
int *r_Next;        // position of next in-neighbor
int *label2pre; // mapping node id -> preoder number
int *pre2label; // mapping preoder number -> node id
int *parent; // parents in the link-eval tree
int *semi;
int *label;
int *dom;
int *spath; // predecessors from sdom-paths
int *dfsparent; // parents in DFS tree

int current_pos;    // next available position in Target
int r_current_pos;  // next available position in r_Target
int nca; // nearest common ancestor of updated edge endpoints
int nextpre; // next preorder number

unsigned long long int lol= 0;

/******************* BUCKET STRUCTURE* ********************/
int *level; // level array
int *idom; // dominator tree
int *affectedQueue; // stores (possibly) affected vertices
int *arcQueue; // stores (possibly) affected vertices
int *levelQueue; // stores (vertex, level) pairs for vertices that change level

int affectedQueueFirst;
int affectedQueueLast;
int arcQueueFirst;
int arcQueueLast;
int levelQueueFirst;
int levelQueueLast;
int minDepth;
int bucketLevel; // max level of a vertex in bucket

bool *visited; // true for visited vertices
bool *affected; // true for affected (or possibly affected by deletion) vertices
bool *ancestor_of_y;

/* ====== new variables ====== */
char file[100];

int *size; // number of descendants for each node in D
int *preorder2labelDominator;
int *label2preorderDominator;
int *dominatorFirst;
int *dominatorTarget;
int *dominatorNext;
int *dfsDominatorDiscovered;
int *derivedOutFirst;
int *derivedOutTarget;
int *derivedOutNext;
int *derivedOutPrev;
int *derivedInFirst;
int *derivedInTarget;
int *derivedInNext;
int *derivedInPrev;
int *derivedArcCounter;
int *derivedGraphInSiblings;
int *derivedInArcsCounter;
int *derivedOutArcsCounter;
int *triples;
int *QList;
int *inQList;
int *criticalPath;
int *topologicalOrder;
int *lowHighHead;
int *lowHighPrevNode;
int *lowHighNextNode;
int *derivedOutLowHighFirst;
int *derivedOutLowHighTarget;
int *derivedOutLowHighPrev;
int *derivedOutLowHighNext;
int *violatingLowHigh;
int *needUpdateLowHigh;
int *needUpdateLowHighSorted;
int *prevIdom;
int *positionInViolatingLowHigh;
int *derivedOutFirstReverse;
int *derivedInFirstReverse;
int *derivedOutLowHighFirstReverse;
int *visitedNodes;
int *nodesInAlreadyCheckedList;
int *derivedInLowHighReverseNode;
int *correspondingGraphArc;
int *correspondingDerivedArc;
int *nextArcWithTheSameDerivedArc;
int *prevArcWithTheSameDerivedArc;
int *skippedFromDFSU;
int *nodesInAffectedNodeSubtree;
int *siblingsInLowHighOrder;

int **derivedInLowHigh;
int **derivedInLowHighReversePosition;

unsigned long long int *lowHighId;

bool *derivedArcFromDominator;
bool *inLowHighOrder;
bool *inLowHighChildrenList;
bool *inViolatingLowHigh;
bool *inNeedUpdateLowHigh;
bool *inNeedUpdateLowHighSorted;
bool *inLevelQueue;
bool *validArc;
bool *inAffectedNodeSubtree;

int skippedFromDFSUCounter;
int dfsDominatorCounter;
int triplesCounter;
int derivedGraphCurrentPosition;
int QListCounter;
int nodesInQList;
int criticalPathCounter;
int lastNodePreorder;
int lastNodePostorder;
int prevLevel;
int alreadyCheckedCurrentPosition;
int topologicalOrderCounter;
int derivedOutLowHighCurrentPosition;
int violatingLowHighCounter;
int needUpdateLowHighCounter;
int needUpdateLowHighSortedCounter;
int visitedNodesCounter;
int nodesInAlreadyCheckedListCounter;
int rootLevel;
int nodesInAffectedNodeSubtreeCounter;
int siblingsInLowHighOrderCounter;
int insertionDeletionFlag; // 0-> deletions, 1->insertions

unsigned long long int maxId;

bool criticalPathFlag;
bool noNewParentFlag;
bool violatingLowHighFlag;
bool executeProcessNeedUpdateLowHighFlag;
bool constructionPhase;

long double representativeIdStep;
long double nextRepresentativeIdPreorder;
long double nextRepresentativeIdPostorder;
/* ============================================*/

struct node* createNewNode(int name){
	struct node* tmpNode= (struct node*)malloc(sizeof(struct node));

	tmpNode->nodesName= name;
	tmpNode->tag= 0;
	tmpNode->leftNode= NULL;
	tmpNode->rightNode= NULL;
	tmpNode->rep= NULL;

	return tmpNode;
}

struct representative* createNewRepresentative(int name){
	struct representative* tmpRep= (struct representative*)malloc(sizeof(struct representative));

	tmpRep->representativesName= name;
	tmpRep->tag= 0;
	tmpRep->leaves= 0;
	tmpRep->nodesListHead= NULL;
	tmpRep->nodesListTail= NULL;
	tmpRep->leftRepresentative= NULL;
	tmpRep->rightRepresentative= NULL;

	return tmpRep;
}

// compute nearest common ancestor
inline int intersectLevel(int v1, int v2){
	int x= v1;
	int y= v2;

	if(v1 == 0) return y;
	if(v2 == 0) return x;
	while(v1 != v2){
		if(level[v1] >= level[v2]) v1= idom[v1];
		if(level[v2]> level[v1]) v2= idom[v2];
	}

	return v1;
}

void resetTriples(){
	int nodes= n+1;
	int edges= m+1;
	triplesCounter= 0;

	for(int i= (3*nodes+3*edges)-1; i >= 0; i--){
		triples[i]= 0;
	}
}

// initialization
void init(int N,int M) {
	current_pos=r_current_pos=1;
	int * buffer= new int[42*N+33*M];

	First=&buffer[0];//new int [N];
	Target=&buffer[N];//new int [M];
	Next=&buffer[N+M];//new int [M];
	r_First=&buffer[N+2*M];// new int[N];
	r_Target=&buffer[2*N+2*M];//new int [M];
	r_Next=&buffer[2*N+3*M];//new int [M];

	arcQueue=&buffer[2*N+4*M];//new int[2*M];
	idom = &buffer[2*N+6*M];//new int [N];
	level = &buffer[3*N+6*M];//new int [N];

	label2pre =&buffer[4*N+6*M];// new int[N];
	pre2label =&buffer[5*N+6*M];// new int[N];

	parent = &buffer[6*N+6*M];//new int[N];
	dfsparent =&buffer[7*N+6*M];// new int[N];
	spath = &buffer[8*N+6*M];//new int[N];
	semi =&buffer[9*N+6*M];// new int[N];
	label =&buffer[10*N+6*M];// new int[N];
	dom = &buffer[11*N+6*M];//new int[N];
	size= &buffer[12*N+6*M];//new int[N];

	preorder2labelDominator= &buffer[13*N+6*M];//new int[N];
	label2preorderDominator= &buffer[14*N+6*M];//new int[N];

	dominatorFirst= &buffer[15*N+6*M];//new int[N];
	dominatorTarget= &buffer[16*N+6*M];//new int[N];
	dominatorNext= &buffer[17*N+6*M];//new int[N];
	dfsDominatorDiscovered= &buffer[18*N+6*M];//new int[N];

	derivedOutFirst= &buffer[19*N+6*M];//new int[N];
	derivedOutTarget= &buffer[20*N+6*M];//new int[M];
	derivedOutNext= &buffer[20*N+7*M];//new int[M];
	derivedOutPrev= &buffer[20*N+8*M];//new int[M];
	derivedInFirst= &buffer[20*N+9*M];//new int[N];
	derivedInTarget= &buffer[21*N+9*M];//new int[M];
	derivedInNext= &buffer[21*N+10*M];//new int[M];
	derivedInPrev= &buffer[21*N+11*M];//new int[M];
	derivedArcCounter= &buffer[21*N+12*M];//new int[M];
	derivedGraphInSiblings= &buffer[21*N+13*M];//new int[N];

	topologicalOrder= &buffer[22*N+13*M];//new int[N];

	lowHighHead= &buffer[23*N+13*M];//new int[N];
	lowHighPrevNode= &buffer[24*N+13*M];//new int[N];
	lowHighNextNode= &buffer[25*N+13*M];//new int[N];

	derivedOutLowHighFirst= &buffer[26*N+13*M];//new int[N];
	derivedOutLowHighTarget= &buffer[27*N+13*M];//new int[2*M];
	derivedOutLowHighPrev= &buffer[27*N+15*M];//new int[2*M];
	derivedOutLowHighNext= &buffer[27*N+17*M];//new int[2*M];

	violatingLowHigh= &buffer[27*N+19*M];//new int[N];
	needUpdateLowHigh= &buffer[28*N+19*M];//new int[N];
	needUpdateLowHighSorted= &buffer[29*N+19*M];//new int[N];
	prevIdom= &buffer[30*N+19*M];//new int[N];
	positionInViolatingLowHigh= &buffer[31*N+19*M];//new int[N];

	derivedOutFirstReverse= &buffer[32*N+19*M];//new int[M];
	derivedInFirstReverse= &buffer[32*N+20*M];//new int[M];
	derivedOutLowHighFirstReverse= &buffer[32*N+21*M];//new int[M];

	visitedNodes= &buffer[32*N+22*M];//new int[N];
	nodesInAlreadyCheckedList= &buffer[33*N+22*M];//new int[N];
	derivedInLowHighReverseNode= &buffer[34*N+22*M];//new int[M];
	correspondingGraphArc= &buffer[34*N+23*M];//new int[M];
	correspondingDerivedArc= &buffer[34*N+24*M];//new int[M];
	nextArcWithTheSameDerivedArc= &buffer[34*N+25*M];//new int[M];
	prevArcWithTheSameDerivedArc= &buffer[34*N+26*M];//new int[M];
	skippedFromDFSU= &buffer[34*N+27*M];//new int[M];
	affectedQueue= &buffer[34*N+28*M];//new int[N];
	levelQueue=&buffer[35*N+28*M];//new int[2*N];
	derivedInArcsCounter= &buffer[37*N+28*M];//new int[M];
	derivedOutArcsCounter= &buffer[37*N+29*M];//new int[M];
	nodesInAffectedNodeSubtree= &buffer[37*N+30*M];//new int[N];
	siblingsInLowHighOrder= &buffer[38*N+30*M];//new int[N];
	triples= &buffer[39*N+30*M];//new int[3*N+3*M];

	QList= new int[N];//new int[N];
	inQList= new int[N];//new int[N];
	criticalPath= new int[N];//new int[N];

	lowHighId= new unsigned long long int[N];//new unsigned long long int[N];

	visited = new bool[N];
	derivedArcFromDominator= new bool[N];//new bool[N];
	inLowHighOrder= new bool[N];//new bool[N];
	inLowHighChildrenList= new bool[N];//new bool[N];
	inViolatingLowHigh= new bool[N];//new bool[N];
	inNeedUpdateLowHigh= new bool[N];//new bool[N];
	inNeedUpdateLowHighSorted= new bool[N];//new bool[N];
	affected= new bool[N];//new bool [N];
	ancestor_of_y= new bool[N];//new bool [N];
	inLevelQueue= new bool[N];//new bool [N];
	validArc= new bool[M];//new bool [M];
	inAffectedNodeSubtree= new bool[N];//new bool [N];

	derivedInLowHigh= new int*[N];
	derivedInLowHighReversePosition= new int*[N];
	for(int i= n; i >= 0; i--){
		derivedInLowHigh[i]=  new int[2];
		derivedInLowHighReversePosition[i]=  new int[2];
	}

	for(int i= n; i >= 0; i--){
		label2pre[i]= pre2label[i]= 0;
		idom[i]= parent[i]= dom[i]= level[i]= 0;
		dfsparent[i]= spath[i]= 0;
		semi[i]= label[i]= i;
		First[i]= r_First[i]= 0;
		size[i]= 1;
		preorder2labelDominator[i]= 0;
		label2preorderDominator[i]= 0;
		dominatorFirst[i]= 0;
		dominatorTarget[i]= dominatorNext[i]= 0;
		dfsDominatorDiscovered[i]= 0;
		derivedOutFirst[i]= 0;
		derivedInFirst[i]= 0;
		derivedGraphInSiblings[i]= 0;
		QList[i]= 0;
		inQList[i]= 0;
		criticalPath[i]= 0;
		topologicalOrder[i]= 0;
		lowHighHead[i]= 0;
		lowHighPrevNode[i]= 0;
		lowHighNextNode[i]= 0;
		lowHighId[i]= 0;
		derivedInLowHigh[i][0]= 0;
		derivedInLowHigh[i][1]= 0;
		derivedInLowHighReversePosition[i][0]= 0;
		derivedInLowHighReversePosition[i][1]= 0;
		derivedOutLowHighFirst[i]= 0;
		violatingLowHigh[i]= 0;
		needUpdateLowHigh[i]= 0;
		needUpdateLowHighSorted[i]= 0;
		prevIdom[i]= 0;
		positionInViolatingLowHigh[i]= 0;
		visitedNodes[i]= 0;
		nodesInAlreadyCheckedList[i]= 0;
		nodesInAffectedNodeSubtree[i]= 0;
		siblingsInLowHighOrder[i]= 0;

		visited[i]= false;
		derivedArcFromDominator[i]= false;
		inLowHighOrder[i]= false;
		inLowHighChildrenList[i]= false;
		inViolatingLowHigh[i]= false;
		inNeedUpdateLowHigh[i]= false;
		inNeedUpdateLowHighSorted[i]= false;
		inLevelQueue[i]= false;
		affected[i]= false;
		ancestor_of_y[i]= false;
		inAffectedNodeSubtree[i]= false;
	}

	for(int i= m; i >= 0; i--) {
		Target[i]=Next[i]=r_Target[i] = r_Next[i]= 0;
		derivedOutTarget[i]= derivedOutNext[i]= derivedOutPrev[i]= derivedArcCounter[i]= 0;
		derivedInTarget[i]= derivedInNext[i]= derivedInPrev[i]= 0;
		derivedInArcsCounter[i]= 0;
		derivedOutArcsCounter[i]= 0;
		derivedOutLowHighTarget[i]= derivedOutLowHighNext[i]= derivedOutLowHighPrev[i]= 0;
		derivedOutFirstReverse[i]= derivedInFirstReverse[i]= derivedOutLowHighFirstReverse[i]= 0;
		derivedInLowHighReverseNode[i]= 0;
		correspondingDerivedArc[i]= 0;
		correspondingGraphArc[i]= 0;
		nextArcWithTheSameDerivedArc[i]= 0;
		prevArcWithTheSameDerivedArc[i]= 0;
		skippedFromDFSU[i]= 0;
		validArc[i]= false;
	}
	for(int i= M; i < 2*M; i++){
		derivedOutLowHighTarget[i]= derivedOutLowHighNext[i]= derivedOutLowHighPrev[i]= 0;
	}

	resetTriples();

	QListCounter= 0;
	nodesInQList= 0;
	criticalPathCounter= 0;
	violatingLowHighCounter= 0;
	lastNodePreorder= 0;
	lastNodePostorder= 0;
	needUpdateLowHighCounter= 0;
	needUpdateLowHighSortedCounter= 0;
	visitedNodesCounter= 0;
	nodesInAlreadyCheckedListCounter= 0;
	nodesInAffectedNodeSubtreeCounter= 0;
	siblingsInLowHighOrderCounter= 0;

	level[r]= 1;
	minDepth= n;
	bucketLevel= N-1;
	dfsDominatorCounter= 1;
	derivedGraphCurrentPosition= 1;
	derivedOutLowHighCurrentPosition= 1;
	alreadyCheckedCurrentPosition= 1;

	criticalPathFlag= false;
	noNewParentFlag= false;
	violatingLowHighFlag= false;
	executeProcessNeedUpdateLowHighFlag= false;
	constructionPhase= true;

	idom[r]= r;
	topologicalOrderCounter= n-1;

	nodesTablePreorder= (struct node**)malloc(N*sizeof(struct node*));
	nodesTablePostorder= (struct node**)malloc(N*sizeof(struct node*));

	for(int i= n; i >= 0; i--){
		nodesTablePreorder[i]= NULL;
		nodesTablePostorder[i]= NULL;
	}

	representativesListHeadPreorder= NULL;
	representativesListTailPostorder= NULL;
	representativesCounterPreorder= 0;
	representativesCounterPostorder= 0;
	nodesPerRepresentative= (int) (log(N)/log(2));
	tagSize= 2;

	maxId= ULLONG_MAX/4;
	representativeIdStep= (long double)(maxId)/(long double)(N/(nodesPerRepresentative/2));
	nextRepresentativeIdPreorder= representativeIdStep;
	nextRepresentativeIdPostorder= representativeIdStep;
}

void createPreorderList(int newNodePreorder){
	struct representative* tmpRep= NULL;
	struct representative* newRep= NULL;
	struct representative* currentRep= NULL;
	struct node* tmpNode= NULL;
	struct node* midNode= NULL;
	struct node* currentNode= NULL;
	int counter= 0;

	if(representativesListHeadPreorder == NULL){
		tmpRep= createNewRepresentative(newNodePreorder);
		representativesListHeadPreorder= tmpRep;
		tmpRep->tag= 0;

		tmpNode= createNewNode(newNodePreorder);
		tmpNode->rep= tmpRep;
		tmpNode->tag= 0;

		tmpRep->nodesListHead= tmpNode;
		tmpRep->nodesListTail= tmpNode;
		tmpRep->leaves++;

		nodesTablePreorder[newNodePreorder]= tmpNode;
		lastNodePreorder= newNodePreorder;
		return;
	}

	tmpNode= createNewNode(newNodePreorder);
	tmpRep= nodesTablePreorder[lastNodePreorder]->rep;

	if(tmpRep->leaves == nodesPerRepresentative){
		newRep= createNewRepresentative(newNodePreorder);

		newRep->tag= (unsigned long long int) (floor(nextRepresentativeIdPreorder));
		nextRepresentativeIdPreorder+= representativeIdStep;
		newRep->leftRepresentative= tmpRep;
		tmpRep->rightRepresentative= newRep;

		midNode= tmpRep->nodesListHead;
		while(counter != tmpRep->leaves/2){
			midNode= midNode->rightNode;
			counter++;
		}
		newRep->representativesName= midNode->nodesName;

		midNode->leftNode->rightNode= NULL;
		midNode->leftNode= NULL;
		newRep->nodesListHead= midNode;

		tmpRep->leaves= counter;
		newRep->leaves= nodesPerRepresentative-counter;

		currentNode= tmpRep->nodesListHead;
		currentNode->tag= 0;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-tmpRep->leaves));

			if(currentNode->rightNode == NULL) tmpRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}

		currentNode= newRep->nodesListHead;
		currentNode->tag= 0;
		currentNode->rep= newRep;
		currentNode= currentNode->rightNode;		
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
			currentNode->rep= newRep;

			if(currentNode->rightNode == NULL) newRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}
	}

	currentNode= nodesTablePreorder[lastNodePreorder];
	tmpNode->rep= currentNode->rep;
	tmpNode->tag= currentNode->tag+(1LL << (nodesPerRepresentative-currentNode->rep->leaves));

	tmpNode->leftNode= currentNode;
	currentNode->rightNode= tmpNode;
	tmpNode->rep->nodesListTail= tmpNode;

	tmpNode->rep->leaves++;

	nodesTablePreorder[newNodePreorder]= tmpNode;
	lastNodePreorder= newNodePreorder;
}

void createPostorderList(int newNodePostorder){
	struct representative* tmpRep= NULL;
	struct representative* newRep= NULL;
	struct representative* currentRep= NULL;
	struct node* tmpNode= NULL;
	struct node* midNode= NULL;
	struct node* currentNode= NULL;
	int counter= 0;

	if(representativesListTailPostorder == NULL){
		tmpRep= createNewRepresentative(newNodePostorder);
		representativesListTailPostorder= tmpRep;
		tmpRep->tag= 0;

		tmpNode= createNewNode(newNodePostorder);
		tmpNode->rep= tmpRep;
		tmpNode->tag= 0;

		tmpRep->nodesListHead= tmpNode;
		tmpRep->nodesListTail= tmpNode;
		tmpRep->leaves++;

		nodesTablePostorder[newNodePostorder]= tmpNode;
		lastNodePostorder= newNodePostorder;
		return;
	}

	tmpNode= createNewNode(newNodePostorder);
	tmpRep= nodesTablePostorder[lastNodePostorder]->rep;

	if(tmpRep->leaves == nodesPerRepresentative){
		newRep= createNewRepresentative(newNodePostorder);
		representativesListTailPostorder= newRep;

		newRep->tag= (unsigned long long int) (floor(nextRepresentativeIdPostorder));
		nextRepresentativeIdPostorder+= representativeIdStep;
		newRep->leftRepresentative= tmpRep;
		tmpRep->rightRepresentative= newRep;

		midNode= tmpRep->nodesListHead;
		while(counter != tmpRep->leaves/2){
			midNode= midNode->rightNode;
			counter++;
		}
		newRep->representativesName= midNode->nodesName;

		midNode->leftNode->rightNode= NULL;
		midNode->leftNode= NULL;
		newRep->nodesListHead= midNode;

		tmpRep->leaves= counter;
		newRep->leaves= nodesPerRepresentative-counter;

		currentNode= tmpRep->nodesListHead;
		currentNode->tag= 0;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-tmpRep->leaves));

			if(currentNode->rightNode == NULL) tmpRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}

		currentNode= newRep->nodesListHead;
		currentNode->tag= 0;
		currentNode->rep= newRep;
		currentNode= currentNode->rightNode;
		while(currentNode != NULL){
			currentNode->tag= currentNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
			currentNode->rep= newRep;

			if(currentNode->rightNode == NULL) newRep->nodesListTail= currentNode;
			currentNode= currentNode->rightNode;
		}
	}

	currentNode= nodesTablePostorder[lastNodePostorder];
	tmpNode->rep= currentNode->rep;
	tmpNode->tag= currentNode->tag+(1LL << (nodesPerRepresentative-currentNode->rep->leaves));

	tmpNode->leftNode= currentNode;
	currentNode->rightNode= tmpNode;
	tmpNode->rep->nodesListTail= tmpNode;

	tmpNode->rep->leaves++;

	nodesTablePostorder[newNodePostorder]= tmpNode;
	lastNodePostorder= newNodePostorder;
}

/******************* INSERT - DELETE ARC FROM GRAPH*********************/
inline int insert_arc_to_graph(int x, int y){
	int returnValue= current_pos;

	if(First[x] == 0){
		Target[current_pos]=y;
		First[x]=current_pos++;
	}else{
		Target[current_pos]=y;
		Next[current_pos]=First[x];
		First[x]=current_pos++;
	}

	if(r_First[y] == 0){
		r_Target[r_current_pos]=x;
		r_First[y]=r_current_pos++;
	}else{
		r_Target[r_current_pos]=x;
		r_Next[r_current_pos]=r_First[y];
		r_First[y]=r_current_pos++;
	}

	if(idom[x] != 0) validArc[returnValue]= true;
	return(returnValue);
}

int findGraphsArcPosition(int src, int trg){
	int tmpArcPosition= First[src];
	while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= Next[tmpArcPosition];
	int tmpArc= Target[tmpArcPosition];

	while(true){
		if(tmpArc == trg){
			return(tmpArcPosition);
		}else{
			tmpArcPosition= Next[tmpArcPosition];
			while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= Next[tmpArcPosition];
			tmpArc= Target[tmpArcPosition];
		}
	}
}

// mode == 0 -> remove and delete arc
// mode == 1 -> remove but keep arc (for unreachable arcs)
inline int delete_arc_from_graph(int x, int y, int mode){
	int i, prev, position;

	if(mode == 0){
		if(Target[First[x]] == y){
			position= First[x];
			First[x]= Next[First[x]];
		}else{
			prev= 0;
			i= First[x];
			while(Target[i] != y){
				prev= i;
				i= Next[i];
			}

			position= i;
			Next[prev]= Next[i];
		}

		if(r_Target[r_First[y]] == x){
			r_First[y]= r_Next[r_First[y]];
		}else{
			prev= 0;
			i= r_First[y];
			while(r_Target[i] != x){
				prev= i;
				i= r_Next[i];
			}

			r_Next[prev]= r_Next[i];
		}
	}else{
		position= findGraphsArcPosition(x, y);
		validArc[position]= false;
	}

	return(position);
}

/******************* BATCH ALGORITHM *********************/
// depth-first search from node k - visits only previously unreachable vertices
// stores arcs to previously reachable vertices to be processed later
void DFSU(int k) {
	int j, selected_node;

	label2pre[k]= (++nextpre);
	pre2label[nextpre]= k;

	j= First[k];
	while(j != 0){
		validArc[j]= true;
		selected_node= Target[j];

		if(label2pre[selected_node]){
			if(constructionPhase == false){
				skippedFromDFSU[skippedFromDFSUCounter]= j;
				skippedFromDFSUCounter++;
			}

			j= Next[j];
			continue;
		}

		if(!idom[selected_node]){
			if(constructionPhase == false){
				skippedFromDFSU[skippedFromDFSUCounter]= j;
				skippedFromDFSUCounter++;
			}

			DFSU(selected_node);
			parent[label2pre[selected_node]]= label2pre[k];
			dfsparent[selected_node]= k;
		}else{
			arcQueue[arcQueueLast++]= k;
			arcQueue[arcQueueLast++]= selected_node;
		}

		j= Next[j];
	}

	topologicalOrder[topologicalOrderCounter]= k;
	topologicalOrderCounter--;
}

inline void rcompress (int v, int *parent, int *label, int c) {
	int p;

	if((p=parent[v])> c){
		rcompress (p, parent, label, c); //does not change parent[v]
		if (label[p] < label[v]) label[v]= label[p];
		parent[v]= parent[p];
	}
}

// depth-first search from node k - visits vertices at level > l
void DFSlevel(int k, int l) {
	int nodeToVisit= 0;
	int position= First[k];
	int node= Target[position];

	label2pre[k]= (++nextpre);
	pre2label[nextpre]= k;

	while(position != 0){
		validArc[position]= true;
		nodeToVisit= node;

		if(label2pre[nodeToVisit]){
			position= Next[position];
			node= Target[position];
			
			continue;       
		}

		if(level[nodeToVisit] > l){
			DFSlevel(nodeToVisit, l);
			parent[label2pre[nodeToVisit]]= label2pre[k];
			dfsparent[nodeToVisit]= k;
		}

		position= Next[position];
		node= Target[position];
	}
}

void relabelRepresentatives(int node, int mode, int totalRepresentatives){
	representative* left= NULL;
	representative* right= NULL;
	representative* stoppingPoint= NULL;
	int counter= 1;
	int level= 1;
	unsigned long long int minId= 0;
	unsigned long long int maxId= 0;
	unsigned long long int idsBetweenRepresentatives= 0;
	unsigned long long int nextId= 0;
	double overflowThreshold= 1/T;
	double density= 0.0;
	bool limitsFlag= false;

	if(mode == 0){ // preorder
		left= nodesTablePreorder[node]->rep;
		right= left->rightRepresentative;
		minId= left->tag;
		(right != NULL) ? maxId= right->tag : maxId= ULLONG_MAX/4;

		if(right != NULL) counter++;
		density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);

		while(overflowThreshold <= density && limitsFlag == false){
			level++;

			if(minId != 0 && (minId%(1LL << level) != 0)){
				minId= minId-(minId%(1LL << level));
			}

			if(maxId <= ULLONG_MAX/4 && (maxId%(1LL << level) != (unsigned long long int)((1LL << level)-1))){
				maxId= minId+(1LL << level)-1;
			}

			if(maxId >= ULLONG_MAX/4) limitsFlag= true;

			while(left->leftRepresentative != NULL && left->leftRepresentative->tag >= minId){
				left= left->leftRepresentative;
				counter++;
			}

			while(right != NULL && right->rightRepresentative != NULL && right->rightRepresentative->tag <= maxId){
				right= right->rightRepresentative;
				counter++;
			}

			density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);
			overflowThreshold= overflowThreshold/T;
		}

		if(limitsFlag == true){
			maxId= ULLONG_MAX/4;
		}

		left->tag= minId;
		idsBetweenRepresentatives= (unsigned long long int)(1/density);

		if(left == nodesTablePreorder[node]->rep){
			nextId= minId+((totalRepresentatives+1)*idsBetweenRepresentatives);
		}else{
			nextId= minId+idsBetweenRepresentatives;
		}

		left= left->rightRepresentative;

		(right == NULL) ? stoppingPoint= NULL : stoppingPoint= right->rightRepresentative;

		while(left != stoppingPoint){
			left->tag= nextId;

			if(left == nodesTablePreorder[node]->rep){
				nextId= nextId+((totalRepresentatives+1)*idsBetweenRepresentatives);
			}else{
				nextId= nextId+idsBetweenRepresentatives;
			}

			left= left->rightRepresentative;
		}
	}else{ // postorder
		right= nodesTablePostorder[node]->rep;
		left= right->leftRepresentative;
		(left != NULL) ? minId= left->tag : minId= 0;
		maxId= right->tag;

		if(left != NULL) counter++;
		density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);

		while(overflowThreshold <= density && limitsFlag == false){
			level++;

			if(minId != 0 && (minId%(1LL << level) != 0)){
				minId= minId-(minId%(1LL << level));
			}

			if(maxId <= ULLONG_MAX/4 && (maxId%(1LL << level) != (unsigned long long int)((1LL << level)-1))){
				maxId= minId+(1LL << level)-1;
			}

			if(maxId >= ULLONG_MAX/4) limitsFlag= true;

			while(left != NULL && left->leftRepresentative != NULL && left->leftRepresentative->tag >= minId){
				left= left->leftRepresentative;
				counter++;
			}

			while(right->rightRepresentative != NULL && right->rightRepresentative->tag <= maxId){
				right= right->rightRepresentative;
				counter++;
			}

			density= (double)((double)counter + (double)totalRepresentatives)/(maxId-minId+1);
			overflowThreshold= overflowThreshold/T;
		}

		if(limitsFlag == true){
			maxId= ULLONG_MAX/4;
		}

		right->tag= maxId;
		idsBetweenRepresentatives= (unsigned long long int)(1/density);

		if(right == nodesTablePostorder[node]->rep){
			nextId= maxId-((totalRepresentatives+1)*idsBetweenRepresentatives);
		}else{
			nextId= maxId-idsBetweenRepresentatives;
		}

		right= right->leftRepresentative;
		(left == NULL) ? stoppingPoint= NULL : stoppingPoint= left->leftRepresentative;

		while(right != stoppingPoint){
			right->tag= nextId;

			if(right == nodesTablePostorder[node]->rep){
				nextId= nextId-((totalRepresentatives+1)*idsBetweenRepresentatives);
			}else{
				nextId= nextId-idsBetweenRepresentatives;
			}

			right= right->leftRepresentative;
		}
	}
}

inline bool isChild(int parent, int child){
	if(parent == child){
		return(true);
	}

	if(nodesTablePreorder[parent]->rep->tag > nodesTablePreorder[child]->rep->tag){
		return (false);
	}else if(nodesTablePostorder[parent]->rep->tag < nodesTablePostorder[child]->rep->tag){
		return (false);
	}else if(nodesTablePreorder[parent]->rep->tag == nodesTablePreorder[child]->rep->tag && nodesTablePreorder[parent]->tag >= nodesTablePreorder[child]->tag){
		return (false);
	}else if(nodesTablePostorder[parent]->rep->tag == nodesTablePostorder[child]->rep->tag && nodesTablePostorder[parent]->tag <= nodesTablePostorder[child]->tag){
		return (false);
	}

	return(true);
}

// mode == 0 -> preorder
// mode == 1 -> postorder
void splitRepresentative(struct node* left, struct node* right, int mode){
	struct node* tmpNode= NULL;
	struct representative* newRep= NULL;
	struct representative* leftRep= left->rep;
	struct representative* rightRep= left->rep->rightRepresentative;
	unsigned long long int idDifference= 0;
	int counter= 0;
	int totalLeaves= left->rep->leaves;

	newRep= createNewRepresentative(right->nodesName);
	if(leftRep == representativesListTailPostorder){
		representativesListTailPostorder= newRep;
	}

	if(rightRep == NULL){
		idDifference= ULLONG_MAX/4 - leftRep->tag;
	}else{
		idDifference= rightRep->tag - leftRep->tag;
	}

	if(idDifference == 1){
		if(mode == 0){
			relabelRepresentatives(leftRep->representativesName, 0, 1);
		}else{
			relabelRepresentatives(rightRep->representativesName, 1, 1);
		}

		if(rightRep == NULL){
			idDifference= ULLONG_MAX/4 - leftRep->tag;
		}else{
			idDifference= rightRep->tag - leftRep->tag;
		}
	}
	newRep->tag= leftRep->tag + (idDifference/2);

	newRep->leftRepresentative= left->rep;
	newRep->rightRepresentative= left->rep->rightRepresentative;
	left->rep->rightRepresentative= newRep;
	if(newRep->rightRepresentative != NULL) newRep->rightRepresentative->leftRepresentative= newRep;
	newRep->nodesListHead= right;
	newRep->nodesListTail= left->rep->nodesListTail;
	right->rep= newRep;
	right->leftNode= NULL;
	left->rightNode= NULL;
	left->rep->nodesListTail= left;

	for(tmpNode= left->rep->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode){
		counter++;
	}

	newRep->leaves= left->rep->leaves-counter;
	left->rep->leaves= counter;

	tmpNode= left->rep->nodesListHead;
	tmpNode->tag= 0;
	tmpNode= tmpNode->rightNode;

	while(tmpNode != NULL){
		tmpNode->tag= tmpNode->leftNode->tag+(1LL << (nodesPerRepresentative-left->rep->leaves));
		tmpNode= tmpNode->rightNode;
	}

	tmpNode= newRep->nodesListHead;
	tmpNode->tag= 0;
	tmpNode->rep= newRep;
	tmpNode= tmpNode->rightNode;

	while(tmpNode != NULL){
		tmpNode->tag= tmpNode->leftNode->tag + (1LL << (nodesPerRepresentative-newRep->leaves));
		tmpNode->rep= newRep;
		tmpNode= tmpNode->rightNode;
	}
}

void mergeRepresentatives(struct representative* leftRep, struct representative* rightRep){
	leftRep->nodesListTail->rightNode= rightRep->nodesListHead;
	rightRep->nodesListHead->leftNode= leftRep->nodesListTail;

	leftRep->leaves= leftRep->leaves+rightRep->leaves;
	leftRep->tag= leftRep->tag+((rightRep->tag-leftRep->tag)/2);
	leftRep->rightRepresentative= rightRep->rightRepresentative;
	leftRep->nodesListTail= rightRep->nodesListTail;
	if(rightRep->rightRepresentative != NULL) rightRep->rightRepresentative->leftRepresentative= leftRep;

	struct node* currentNode= leftRep->nodesListHead;
	currentNode->tag= 0;
	currentNode= currentNode->rightNode;
	currentNode->rep= leftRep;

	while(currentNode != NULL){
		currentNode->tag= currentNode->leftNode->tag+(1LL << (nodesPerRepresentative-leftRep->leaves));
		currentNode->rep= leftRep;

		currentNode= currentNode->rightNode;
	}

	if(rightRep == representativesListTailPostorder) representativesListTailPostorder= leftRep;
}

void addToPreorderPostorderLists(int x, int y){// y is the new idom of x (idom[x] == y)
	node* leftNodePreorder= nodesTablePreorder[y];
	node* rightNodePreorder= leftNodePreorder->rightNode;
	node* rightNodePostorder= NULL;
	node* leftNodePostorder= NULL;
	node* newNode= NULL;
	node* tmpNode= NULL;

	representative* leftRepresentativePreorder= leftNodePreorder->rep;
	representative* rightRepresentativePreorder= leftRepresentativePreorder->rightRepresentative;
	representative* rightRepresentativePostorder= NULL;
	representative* leftRepresentativePostorder= NULL;
	representative* newRep= NULL;

	unsigned long long int idDifferencePreorder= 0;
	unsigned long long int idDifferencePostorder= 0;
	unsigned long long int idsBetweenNodes= 0;

	bool newRepFlag= false;

	// postorder (traversing preorder list (it's faster))
	rightNodePostorder= nodesTablePreorder[y];
	if(rightNodePostorder == NULL){
		if(nodesTablePreorder[y]->rep->rightRepresentative == NULL){ // only y in preorder-postorder lists
			rightNodePostorder= nodesTablePreorder[y];
		}else{
			rightNodePostorder= nodesTablePreorder[y]->rep->rightRepresentative->nodesListHead;
		}
	}

	tmpNode= rightNodePostorder->rightNode;
	if(tmpNode == NULL && rightNodePostorder->rep->rightRepresentative != NULL) tmpNode= rightNodePostorder->rep->rightRepresentative->nodesListHead;
	
	// slower when i use representatives to traverse preorder (i have to call isChild in this case which is slower)
	while(tmpNode != NULL){
		if(level[tmpNode->nodesName] > level[rightNodePostorder->nodesName]){
			rightNodePostorder= tmpNode;

			tmpNode= rightNodePostorder->rightNode;
			if(tmpNode == NULL && rightNodePostorder->rep->rightRepresentative != NULL) tmpNode= rightNodePostorder->rep->rightRepresentative->nodesListHead;
		}else{
			break;
		}
	}

	rightNodePostorder= nodesTablePostorder[rightNodePostorder->nodesName]; // rightNodePostorder was pointer to a preorder node
	rightRepresentativePostorder= rightNodePostorder->rep;
	
	leftNodePostorder= rightNodePostorder->leftNode;
	if(leftNodePostorder == NULL && rightNodePostorder->rep->leftRepresentative != NULL) leftNodePostorder= rightNodePostorder->rep->leftRepresentative->nodesListTail;
	if(leftNodePostorder != NULL) leftRepresentativePostorder= leftNodePostorder->rep; // leftNodePostorder can be NULL

	if(leftRepresentativePostorder == rightRepresentativePostorder){
		if(leftRepresentativePostorder->leaves == nodesPerRepresentative){
			splitRepresentative(leftNodePostorder, rightNodePostorder, 1);
			rightRepresentativePostorder= rightNodePostorder->rep;
		}

		newRep= leftRepresentativePostorder;
	}else{
		if(rightRepresentativePostorder->leaves < nodesPerRepresentative){
			newRep= rightRepresentativePostorder;
		}else if(leftRepresentativePostorder != NULL && leftRepresentativePostorder->leaves < nodesPerRepresentative){
			newRep= leftRepresentativePostorder;
		}else{
			newRepFlag= true;
			newRep= createNewRepresentative(x);

			if(leftRepresentativePostorder == NULL){
				idDifferencePostorder= rightRepresentativePostorder->tag;
			}else{
				idDifferencePostorder= rightRepresentativePostorder->tag - leftRepresentativePostorder->tag;
			}

			if(idDifferencePostorder <= 1){
				relabelRepresentatives(rightNodePostorder->nodesName, 1, 1);

				if(leftRepresentativePostorder == NULL){
					idDifferencePostorder= rightRepresentativePostorder->tag;
				}else{
					idDifferencePostorder= rightRepresentativePostorder->tag - leftRepresentativePostorder->tag;
				}
			}
		}
	}

	newNode= createNewNode(x);
	nodesTablePostorder[x]= newNode;
	newNode->rep= newRep;

	if(newRepFlag == true){
		newRep->nodesListHead= newNode;
		newRep->nodesListTail= newNode;
		newRep->leaves= 1;
		newRep->tag= rightRepresentativePostorder->tag - idDifferencePostorder/2;

		if(leftRepresentativePostorder == NULL){
			rightRepresentativePostorder->leftRepresentative= newRep;
			newRep->rightRepresentative= rightRepresentativePostorder;

			newRep->leftRepresentative= NULL;
		}else{
			rightRepresentativePostorder->leftRepresentative= newRep;
			newRep->rightRepresentative= rightRepresentativePostorder;

			leftRepresentativePostorder->rightRepresentative=newRep;
			newRep->leftRepresentative= leftRepresentativePostorder;
		}
	}else{
		if(leftRepresentativePostorder == rightRepresentativePostorder){
			newRep->leaves= newRep->leaves+1;
			newNode->tag= leftNodePostorder->tag + (rightNodePostorder->tag - leftNodePostorder->tag) / 2;

			newNode->rightNode= rightNodePostorder;
			newNode->leftNode= leftNodePostorder;
			rightNodePostorder->leftNode= newNode;
			leftNodePostorder->rightNode= newNode;		
		}else if(newRep == leftRepresentativePostorder){
			newRep->leaves= newRep->leaves+1;
			newRep->nodesListTail= newNode;
			newNode->tag= leftNodePostorder->tag + (ULLONG_MAX/4 - leftNodePostorder->tag) / 2;

			newNode->leftNode= leftNodePostorder;
			leftNodePostorder->rightNode= newNode;		
		}else{ // newRep == rightRepresentativePostorder
			newRep->leaves= newRep->leaves+1;
			newRep->nodesListHead= newNode;
			newRep->representativesName= newNode->nodesName;

			if(rightNodePostorder->rightNode != NULL){
				rightNodePostorder->tag= rightNodePostorder->rightNode->tag / 2;
			}else{
				rightNodePostorder->tag= 1LL << (nodesPerRepresentative-1);
			}

			newNode->rightNode= rightNodePostorder;
			rightNodePostorder->leftNode= newNode;
		}
	}

	// preorder
	newNode= createNewNode(x);
	nodesTablePreorder[x]= newNode;

	if(leftRepresentativePreorder->leaves != nodesPerRepresentative){		
		newNode->rep= leftRepresentativePreorder;
		if(rightNodePreorder == NULL){
			newNode->tag= leftNodePreorder->tag + (ULLONG_MAX/4 - leftNodePreorder->tag) / 2;
		}else{
			newNode->tag= leftNodePreorder->tag + (rightNodePreorder->tag - leftNodePreorder->tag) / 2;
		}

		newNode->rightNode= rightNodePreorder;
		newNode->leftNode= leftNodePreorder;
		if(leftNodePreorder != NULL) leftNodePreorder->rightNode= newNode;
		if(rightNodePreorder != NULL) rightNodePreorder->leftNode= newNode;

		if(leftRepresentativePreorder->nodesListTail == leftNodePreorder) leftRepresentativePreorder->nodesListTail= newNode;
		leftRepresentativePreorder->leaves++; 
	}else{
		node* tmpNode= leftRepresentativePreorder->nodesListHead;
		for(int i= 0; i< nodesPerRepresentative/2; i++) tmpNode= tmpNode->rightNode;

		splitRepresentative(tmpNode, tmpNode->rightNode, 0);

		leftNodePreorder= nodesTablePreorder[y];
		rightNodePreorder= leftNodePreorder->rightNode;
		leftRepresentativePreorder= leftNodePreorder->rep;
		rightRepresentativePreorder= leftRepresentativePreorder->rightRepresentative;

		newNode->rep= leftRepresentativePreorder;
		if(rightNodePreorder == NULL){
			newNode->tag= leftNodePreorder->tag + (ULLONG_MAX/4 - leftNodePreorder->tag) / 2;
		}else{
			newNode->tag= leftNodePreorder->tag + (rightNodePreorder->tag - leftNodePreorder->tag) / 2;
		}

		newNode->rightNode= rightNodePreorder;
		newNode->leftNode= leftNodePreorder;
		if(leftNodePreorder != NULL) leftNodePreorder->rightNode= newNode;
		if(rightNodePreorder != NULL) rightNodePreorder->leftNode= newNode;

		if(leftRepresentativePreorder->nodesListTail == leftNodePreorder) leftRepresentativePreorder->nodesListTail= newNode;
		leftRepresentativePreorder->leaves++;
	}
}

// compute dominator tree rooted at s and consisting of vertices in levels >= l
// mode == 0 -> construction
// mode == 1 -> execution time
void snca(int s, int l, int mode) {
	int i, j, selected_node;

	nextpre= 0;
	if(l < 0){
		DFSU(s);
	}else{
		DFSlevel(s, l);
	}

	int N= nextpre;
	for(i= 1; i <= N; i++) {
		label[i]= semi[i]= i;
	}

	// process the vertices in reverse preorder
	for (i = N; i > 1; i--) {
		dom[i] = parent[i];
		/*---------------------------------------------
		| check incoming arcs, update semi-dominators
		*--------------------------------------------*/
		int k = pre2label[i];

		j= r_First[k];
		while(j != 0 && validArc[j] == false) j= r_Next[j];
		while(j != 0){
			selected_node= r_Target[j];
			int v= label2pre[selected_node]; //v is the source of the arc

			if((v) && (level[selected_node] >= l)){
				int u;

				if(v <= i){
					u= v;//v is an ancestor of i
				}else{
					rcompress(v, parent, label, i);
					u= label[v];
				}

				if(semi[u] < semi[i]){
					semi[i]= semi[u];
					spath[k]= selected_node;
				}
			}

			j = r_Next[j];
			while(j != 0 && validArc[j] == false) j= r_Next[j];
		}

		label[i] = semi[i];
	}

	/*-----------------------------------------------------------
	| compute dominators using idom[w]=NCA(I,parent[w],sdom[w])
	*----------------------------------------------------------*/
	dom[1]= 1;
	for(i= 2; i <= N; i++) {
		int j= dom[i];

		while(j> semi[i]){
			j= dom[j];
		}

		dom[i]= j;

		if(l != -1 && idom[pre2label[i]] != pre2label[dom[i]]){
			int tmpLevel= level[idom[pre2label[i]]];
			int tmpNode= idom[pre2label[i]];

			while(tmpLevel != 0){
				size[tmpNode]-= size[pre2label[i]];

				tmpNode= idom[tmpNode];
				tmpLevel--;
			}

			idom[pre2label[i]]= pre2label[dom[i]];
			level[pre2label[i]]= level[pre2label[dom[i]]] + 1;
		}else{
			idom[pre2label[i]]= pre2label[dom[i]];
			level[pre2label[i]]= level[pre2label[dom[i]]] + 1;
		}

		if(mode == 1) addToPreorderPostorderLists(pre2label[i], idom[pre2label[i]]);
	}

	// reset
	for(i= 1; i <= N; i++) {
		int k= pre2label[i];

		label2pre[k]= pre2label[i]= parent[i]= dom[i]= 0;
	}
}

/******************* DELETION ALGORITHM *********************/
// checks if y is still reachable after the deletion of (x,y)
bool isReachable(int y) {
	int j, node_to_visit;
	int support;

	j= r_First[y];
	while(j != 0 && validArc[j] == false) j= r_Next[j];
	while(j != 0){
		node_to_visit = r_Target[j];

		if(!idom[node_to_visit]){// node_to_visit is unreachable
			j= r_Next[j];
			while(j != 0 && validArc[j] == false) j= r_Next[j];
			continue;
		}

		support= intersectLevel(y, node_to_visit);
		if(support != y) {
			return true;
		}

		j = r_Next[j];
		while(j != 0 && validArc[j] == false) j= r_Next[j];
	}

	return false;
}

int addToDerivedGraph(int x, int y){
	bool flag= false;
	int tmpPosition= 0, tmpNode= 0;
	int derivedOutArcPosition= derivedGraphCurrentPosition;
	int derivedInArcPosition= derivedGraphCurrentPosition;
	int returnValue= derivedGraphCurrentPosition;

	if(derivedInArcsCounter[y] < derivedOutArcsCounter[x]){
		if(derivedInFirst[y] == 0){
			derivedArcCounter[derivedGraphCurrentPosition]++;
			derivedInTarget[derivedGraphCurrentPosition]= x;
			derivedInFirst[y]= derivedGraphCurrentPosition;
			derivedInFirstReverse[derivedGraphCurrentPosition]= y;

			derivedInArcsCounter[y]++;
			derivedOutArcsCounter[x]++;

			derivedGraphCurrentPosition++;
		}else{
			tmpPosition= derivedInFirst[y];

			while(flag == false && tmpPosition != 0){
				if(derivedInTarget[tmpPosition] == x){
					derivedArcCounter[tmpPosition]++;
					flag= true; // derived arc (x,y) already exist

					derivedInArcPosition= tmpPosition;
				}else{
					tmpPosition= derivedInNext[tmpPosition];
				}
			}

			returnValue= derivedInArcPosition;

			if(flag == false){
				derivedArcCounter[derivedGraphCurrentPosition]++;
				derivedInTarget[derivedGraphCurrentPosition]= x;
				derivedInNext[derivedGraphCurrentPosition]= derivedInFirst[y];
				derivedInPrev[derivedInFirst[y]]= derivedGraphCurrentPosition;
				derivedInFirstReverse[derivedInFirst[y]]= 0;
				derivedInFirst[y]= derivedGraphCurrentPosition;
				derivedInFirstReverse[derivedGraphCurrentPosition]= y;

				derivedInArcsCounter[y]++;
				derivedOutArcsCounter[x]++;

				derivedGraphCurrentPosition++;
			}
		}

		if(flag == false){
			if(derivedOutFirst[x] == 0){
				derivedOutTarget[derivedOutArcPosition]= y;
				derivedOutFirst[x]= derivedOutArcPosition;
				derivedOutFirstReverse[derivedOutArcPosition]= x;
			}else{
				derivedOutTarget[derivedOutArcPosition]= y;
				derivedOutNext[derivedOutArcPosition]= derivedOutFirst[x];
				derivedOutPrev[derivedOutFirst[x]]= derivedOutArcPosition;
				derivedOutFirstReverse[derivedOutFirst[x]]= 0;
				derivedOutFirst[x]= derivedOutArcPosition;
				derivedOutFirstReverse[derivedOutArcPosition]= x;
			}
		}
	}else{
		if(derivedOutFirst[x] == 0){
			derivedArcCounter[derivedGraphCurrentPosition]++;
			derivedOutTarget[derivedGraphCurrentPosition]= y;
			derivedOutFirst[x]= derivedGraphCurrentPosition;
			derivedOutFirstReverse[derivedGraphCurrentPosition]= x;

			derivedInArcsCounter[y]++;
			derivedOutArcsCounter[x]++;

			derivedGraphCurrentPosition++;
		}else{
			tmpPosition= derivedOutFirst[x];

			while(flag == false && tmpPosition != 0){
				if(derivedOutTarget[tmpPosition] == y){
					derivedArcCounter[tmpPosition]++;
					flag= true; // derived arc (x,y) already exist

					derivedOutArcPosition= tmpPosition;
				}else{
					tmpPosition= derivedOutNext[tmpPosition];
				}
			}

			returnValue= derivedOutArcPosition;

			if(flag == false){
				derivedArcCounter[derivedGraphCurrentPosition]++;
				derivedOutTarget[derivedGraphCurrentPosition]= y;
				derivedOutNext[derivedGraphCurrentPosition]= derivedOutFirst[x];
				derivedOutPrev[derivedOutFirst[x]]= derivedGraphCurrentPosition;
				derivedOutFirstReverse[derivedOutFirst[x]]= 0;
				derivedOutFirst[x]= derivedGraphCurrentPosition;
				derivedOutFirstReverse[derivedGraphCurrentPosition]= x;

				derivedInArcsCounter[y]++;
				derivedOutArcsCounter[x]++;

				derivedGraphCurrentPosition++;
			}
		}

		if(flag == false){
			if(derivedInFirst[y] == 0){
				derivedInTarget[derivedInArcPosition]= x;
				derivedInFirst[y]= derivedInArcPosition;
				derivedInFirstReverse[derivedInArcPosition]= y;
			}else{
				derivedInTarget[derivedInArcPosition]= x;
				derivedInNext[derivedInArcPosition]= derivedInFirst[y];
				derivedInPrev[derivedInFirst[y]]= derivedInArcPosition;
				derivedInFirstReverse[derivedInFirst[y]]= 0;
				derivedInFirst[y]= derivedInArcPosition;
				derivedInFirstReverse[derivedInArcPosition]= y;
			}
		}
	}

	if(flag == false && level[x] == level[y] && idom[x] == idom[y]){
		derivedGraphInSiblings[y]++;
	}
	
	if(x == idom[y]){
		derivedArcFromDominator[y]= true;
	}

	return(returnValue);
}

void addToDerivedOutLowHigh(int node, int parent){
	if(derivedOutLowHighFirst[parent] == 0){
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= node;
		derivedOutLowHighFirst[parent]= derivedOutLowHighCurrentPosition;
		derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= parent;
		derivedOutLowHighCurrentPosition++;
	}else{
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= node;
		derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= derivedOutLowHighFirst[parent];
		derivedOutLowHighPrev[derivedOutLowHighFirst[parent]]= derivedOutLowHighCurrentPosition;
		
		derivedOutLowHighFirstReverse[derivedOutLowHighFirst[parent]]= 0;
		derivedOutLowHighFirst[parent]= derivedOutLowHighCurrentPosition;
		derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= parent;
		derivedOutLowHighCurrentPosition++;
	}
}

int removeFromDerivedOutLowHigh(int node, int parent){
	int tmpPosition= 0;

	if(derivedInLowHigh[node][0] == parent){
		tmpPosition= derivedInLowHighReversePosition[node][0];
	}else{
		tmpPosition= derivedInLowHighReversePosition[node][1];
	}

	if(derivedOutLowHighTarget[derivedOutLowHighFirst[parent]] == node){
		if(derivedOutLowHighNext[tmpPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[tmpPosition]]= 0;
		derivedOutLowHighFirstReverse[derivedOutLowHighFirst[parent]]= 0;
		derivedOutLowHighFirst[parent]= derivedOutLowHighNext[tmpPosition];
		derivedOutLowHighFirstReverse[derivedOutLowHighNext[tmpPosition]]= parent;

		derivedOutLowHighCurrentPosition--;
		if(derivedOutLowHighCurrentPosition != tmpPosition){
			derivedOutLowHighTarget[tmpPosition]= derivedOutLowHighTarget[derivedOutLowHighCurrentPosition];
			derivedOutLowHighNext[tmpPosition]= derivedOutLowHighNext[derivedOutLowHighCurrentPosition];
			derivedOutLowHighPrev[tmpPosition]= derivedOutLowHighPrev[derivedOutLowHighCurrentPosition];

			if(derivedOutLowHighPrev[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]]= tmpPosition;
			if(derivedOutLowHighNext[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[derivedOutLowHighCurrentPosition]]= tmpPosition;
		}

		int tmp= derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition];
		if(derivedInLowHighReversePosition[tmp][0] == derivedOutLowHighCurrentPosition){
			derivedInLowHighReversePosition[tmp][0]= tmpPosition;
			derivedInLowHighReverseNode[tmpPosition]= tmp;
		}else if(derivedInLowHighReversePosition[tmp][1] == derivedOutLowHighCurrentPosition){
			derivedInLowHighReversePosition[tmp][1]= tmpPosition;
			derivedInLowHighReverseNode[tmpPosition]= tmp;
		}

		if(derivedInLowHigh[node][0] == parent){
			derivedInLowHigh[node][0]= 0;
			derivedInLowHighReversePosition[node][0]= 0;
		}else{
			derivedInLowHigh[node][1]= 0;
			derivedInLowHighReversePosition[node][1]= 0;
		}		

		derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
		derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= 0;

		if(derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition] != 0){
			derivedOutLowHighFirst[derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]]= tmpPosition;
			derivedOutLowHighFirstReverse[tmpPosition]= derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition];
			derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= 0;
		}
	}else{
		if(derivedOutLowHighTarget[tmpPosition] != 0){
			if(derivedOutLowHighPrev[tmpPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[tmpPosition]]= derivedOutLowHighNext[tmpPosition];
			if(derivedOutLowHighNext[tmpPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[tmpPosition]]= derivedOutLowHighPrev[tmpPosition];

			derivedOutLowHighCurrentPosition--;
			if(derivedOutLowHighCurrentPosition != tmpPosition){
				derivedOutLowHighTarget[tmpPosition]= derivedOutLowHighTarget[derivedOutLowHighCurrentPosition];
				derivedOutLowHighNext[tmpPosition]= derivedOutLowHighNext[derivedOutLowHighCurrentPosition];
				derivedOutLowHighPrev[tmpPosition]= derivedOutLowHighPrev[derivedOutLowHighCurrentPosition];

				if(derivedOutLowHighPrev[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighNext[derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]]= tmpPosition;
				if(derivedOutLowHighNext[derivedOutLowHighCurrentPosition] != 0) derivedOutLowHighPrev[derivedOutLowHighNext[derivedOutLowHighCurrentPosition]]= tmpPosition;
			}

			int tmp= derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition];
			if(derivedInLowHighReversePosition[tmp][0] == derivedOutLowHighCurrentPosition){
				derivedInLowHighReversePosition[tmp][0]= tmpPosition;
				derivedInLowHighReverseNode[tmpPosition]= tmp;
			}else if(derivedInLowHighReversePosition[tmp][1] == derivedOutLowHighCurrentPosition){
				derivedInLowHighReversePosition[tmp][1]= tmpPosition;
				derivedInLowHighReverseNode[tmpPosition]= tmp;
			}

			if(derivedInLowHigh[node][0] == parent){
				derivedInLowHigh[node][0]= 0;
				derivedInLowHighReversePosition[node][0]= 0;
			}else if(derivedInLowHigh[node][1] == parent){
				derivedInLowHigh[node][1]= 0;
				derivedInLowHighReversePosition[node][1]= 0;
			}		

			derivedOutLowHighNext[derivedOutLowHighCurrentPosition]= 0;
			derivedOutLowHighPrev[derivedOutLowHighCurrentPosition]= 0;
			derivedOutLowHighTarget[derivedOutLowHighCurrentPosition]= 0;

			if(derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition] != 0){
				derivedOutLowHighFirst[derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]]= tmpPosition;
				derivedOutLowHighFirstReverse[tmpPosition]= derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition];
				derivedOutLowHighFirstReverse[derivedOutLowHighCurrentPosition]= 0;
			}
		}
	}

	return(tmpPosition);
}

// returnValue
// -1 -> edge doesn't exist
//  0 -> multiple copies of derived arc
//  1 -> derived arc has been removed
int removeFromDerivedGraph(int derivedArcPosition, bool calledFromDeleteReachable){
	int derivedX= derivedInTarget[derivedArcPosition];
	int derivedY= derivedOutTarget[derivedArcPosition];
	int returnValue= 1;

	violatingLowHighFlag= false;

	if(derivedOutFirst[derivedX] == derivedArcPosition){
		if(derivedArcCounter[derivedArcPosition] == 1){
			derivedOutArcsCounter[derivedInTarget[derivedArcPosition]]--;
			derivedInArcsCounter[derivedOutTarget[derivedArcPosition]]--;

			// derivedOut
			if(derivedOutNext[derivedArcPosition] != 0) derivedOutPrev[derivedOutNext[derivedArcPosition]]= 0;
			derivedOutFirstReverse[derivedOutFirst[derivedX]]= 0;
			derivedOutFirst[derivedX]= derivedOutNext[derivedArcPosition];
			derivedOutFirstReverse[derivedOutNext[derivedArcPosition]]= derivedX;

			// derivedIn
			if(derivedInFirst[derivedY] == derivedArcPosition){
				if(derivedInNext[derivedArcPosition] != 0) derivedInPrev[derivedInNext[derivedArcPosition]]= 0;
				derivedInFirstReverse[derivedInFirst[derivedY]]= 0;
				derivedInFirst[derivedY]= derivedInNext[derivedArcPosition];
				derivedInFirstReverse[derivedInNext[derivedArcPosition]]= derivedY;
			}else{
				if(derivedInNext[derivedArcPosition] != 0) derivedInPrev[derivedInNext[derivedArcPosition]]= derivedInPrev[derivedArcPosition];
				if(derivedInPrev[derivedArcPosition] != 0) derivedInNext[derivedInPrev[derivedArcPosition]]= derivedInNext[derivedArcPosition];
			}

			derivedGraphCurrentPosition--;
			if(derivedGraphCurrentPosition != derivedArcPosition){
				derivedArcCounter[derivedArcPosition]= derivedArcCounter[derivedGraphCurrentPosition];
				derivedOutTarget[derivedArcPosition]= derivedOutTarget[derivedGraphCurrentPosition];
				derivedOutNext[derivedArcPosition]= derivedOutNext[derivedGraphCurrentPosition];
				derivedOutPrev[derivedArcPosition]= derivedOutPrev[derivedGraphCurrentPosition];
				if(derivedOutPrev[derivedGraphCurrentPosition] != 0) derivedOutNext[derivedOutPrev[derivedGraphCurrentPosition]]= derivedArcPosition;
				if(derivedOutNext[derivedGraphCurrentPosition] != 0) derivedOutPrev[derivedOutNext[derivedGraphCurrentPosition]]= derivedArcPosition;

				derivedInTarget[derivedArcPosition]= derivedInTarget[derivedGraphCurrentPosition];
				derivedInNext[derivedArcPosition]= derivedInNext[derivedGraphCurrentPosition];
				derivedInPrev[derivedArcPosition]= derivedInPrev[derivedGraphCurrentPosition];
				if(derivedInPrev[derivedGraphCurrentPosition] != 0) derivedInNext[derivedInPrev[derivedGraphCurrentPosition]]= derivedArcPosition;
				if(derivedInNext[derivedGraphCurrentPosition] != 0) derivedInPrev[derivedInNext[derivedGraphCurrentPosition]]= derivedArcPosition;
			}

			if(derivedOutFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedOutFirst[derivedOutFirstReverse[derivedGraphCurrentPosition]]= derivedArcPosition;
				derivedOutFirstReverse[derivedArcPosition]= derivedOutFirstReverse[derivedGraphCurrentPosition];
				derivedOutFirstReverse[derivedGraphCurrentPosition]= 0;
			}

			if(derivedInFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedInFirst[derivedInFirstReverse[derivedGraphCurrentPosition]]= derivedArcPosition;
				derivedInFirstReverse[derivedArcPosition]= derivedInFirstReverse[derivedGraphCurrentPosition];
				derivedInFirstReverse[derivedGraphCurrentPosition]= 0;
			}			

			int tmpPosition= correspondingGraphArc[derivedGraphCurrentPosition];
			while(tmpPosition != 0){
				correspondingDerivedArc[tmpPosition]= derivedArcPosition;
				tmpPosition= nextArcWithTheSameDerivedArc[tmpPosition];
			}
			correspondingGraphArc[derivedArcPosition]= correspondingGraphArc[derivedGraphCurrentPosition];
			
			derivedArcCounter[derivedGraphCurrentPosition]= 0;
			derivedOutTarget[derivedGraphCurrentPosition]= 0;
			derivedOutNext[derivedGraphCurrentPosition]= 0;
			derivedOutPrev[derivedGraphCurrentPosition]= 0;
			derivedInTarget[derivedGraphCurrentPosition]= 0;
			derivedInNext[derivedGraphCurrentPosition]= 0;
			derivedInPrev[derivedGraphCurrentPosition]= 0;
			correspondingGraphArc[derivedGraphCurrentPosition]= 0;
		}else{
			derivedArcCounter[derivedArcPosition]--;
			returnValue= 0;
		}
	}else{
		if(derivedArcCounter[derivedArcPosition] == 1){
			derivedOutArcsCounter[derivedInTarget[derivedArcPosition]]--;
			derivedInArcsCounter[derivedOutTarget[derivedArcPosition]]--;

			// derivedOut
			if(derivedOutNext[derivedArcPosition] != 0) derivedOutPrev[derivedOutNext[derivedArcPosition]]= derivedOutPrev[derivedArcPosition];
			if(derivedOutPrev[derivedArcPosition] != 0) derivedOutNext[derivedOutPrev[derivedArcPosition]]= derivedOutNext[derivedArcPosition];

			// derivedIn
			if(derivedInFirst[derivedY] == derivedArcPosition){
				if(derivedInNext[derivedArcPosition] != 0) derivedInPrev[derivedInNext[derivedArcPosition]]= 0;
				derivedInFirstReverse[derivedInFirst[derivedY]]= 0;
				derivedInFirst[derivedY]= derivedInNext[derivedArcPosition];
				derivedInFirstReverse[derivedInNext[derivedArcPosition]]= derivedY;
			}else{
				if(derivedInNext[derivedArcPosition] != 0) derivedInPrev[derivedInNext[derivedArcPosition]]= derivedInPrev[derivedArcPosition];
				if(derivedInPrev[derivedArcPosition] != 0) derivedInNext[derivedInPrev[derivedArcPosition]]= derivedInNext[derivedArcPosition];
			}

			derivedGraphCurrentPosition--;
			if(derivedGraphCurrentPosition != derivedArcPosition){
				derivedArcCounter[derivedArcPosition]= derivedArcCounter[derivedGraphCurrentPosition];

				derivedOutTarget[derivedArcPosition]= derivedOutTarget[derivedGraphCurrentPosition];
				derivedOutNext[derivedArcPosition]= derivedOutNext[derivedGraphCurrentPosition];
				derivedOutPrev[derivedArcPosition]= derivedOutPrev[derivedGraphCurrentPosition];
				if(derivedOutPrev[derivedGraphCurrentPosition] != 0) derivedOutNext[derivedOutPrev[derivedGraphCurrentPosition]]= derivedArcPosition;
				if(derivedOutNext[derivedGraphCurrentPosition] != 0) derivedOutPrev[derivedOutNext[derivedGraphCurrentPosition]]= derivedArcPosition;

				derivedInTarget[derivedArcPosition]= derivedInTarget[derivedGraphCurrentPosition];
				derivedInNext[derivedArcPosition]= derivedInNext[derivedGraphCurrentPosition];
				derivedInPrev[derivedArcPosition]= derivedInPrev[derivedGraphCurrentPosition];
				if(derivedInPrev[derivedGraphCurrentPosition] != 0) derivedInNext[derivedInPrev[derivedGraphCurrentPosition]]= derivedArcPosition;
				if(derivedInNext[derivedGraphCurrentPosition] != 0) derivedInPrev[derivedInNext[derivedGraphCurrentPosition]]= derivedArcPosition;
			}

			if(derivedOutFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedOutFirst[derivedOutFirstReverse[derivedGraphCurrentPosition]]= derivedArcPosition;
				derivedOutFirstReverse[derivedArcPosition]= derivedOutFirstReverse[derivedGraphCurrentPosition];
				derivedOutFirstReverse[derivedGraphCurrentPosition]= 0;
			}

			if(derivedInFirstReverse[derivedGraphCurrentPosition] != 0){
				derivedInFirst[derivedInFirstReverse[derivedGraphCurrentPosition]]= derivedArcPosition;
				derivedInFirstReverse[derivedArcPosition]= derivedInFirstReverse[derivedGraphCurrentPosition];
				derivedInFirstReverse[derivedGraphCurrentPosition]= 0;
			}			

			int tmpPosition= correspondingGraphArc[derivedGraphCurrentPosition];
			while(tmpPosition != 0){
				correspondingDerivedArc[tmpPosition]= derivedArcPosition;
				tmpPosition= nextArcWithTheSameDerivedArc[tmpPosition];
			}
			correspondingGraphArc[derivedArcPosition]= correspondingGraphArc[derivedGraphCurrentPosition];

			derivedArcCounter[derivedGraphCurrentPosition]= 0;
			derivedOutTarget[derivedGraphCurrentPosition]= 0;
			derivedOutNext[derivedGraphCurrentPosition]= 0;
			derivedOutPrev[derivedGraphCurrentPosition]= 0;
			derivedInTarget[derivedGraphCurrentPosition]= 0;
			derivedInNext[derivedGraphCurrentPosition]= 0;
			derivedInPrev[derivedGraphCurrentPosition]= 0;
			correspondingGraphArc[derivedGraphCurrentPosition]= 0;
		}else{
			derivedArcCounter[derivedArcPosition]--;
			returnValue= 0;
		}
	}

	bool arcWasFromDominator= false; // in this case we have to find two derived arcs
	int lowerNode= 0;
	int higherNode= 0;

	if(derivedX == idom[derivedY] && returnValue == 1){
		derivedArcFromDominator[derivedY]= false;
		arcWasFromDominator= true; 
	}

	if(calledFromDeleteReachable == true  && returnValue == 1){
		if((derivedInLowHigh[derivedY][0] == derivedX || derivedInLowHigh[derivedY][1] == derivedX)){
			int tmpPosition= derivedInFirst[derivedY];
			int tmpNode= derivedInTarget[tmpPosition];

			if(arcWasFromDominator == false){
				if(lowHighId[derivedX] < lowHighId[derivedY]){
					while(tmpPosition != 0){
						if(lowHighId[tmpNode] < lowHighId[derivedY] && inViolatingLowHigh[tmpNode] == false){
							lowerNode= derivedInTarget[tmpPosition];
							break;
						}else{
							tmpPosition= derivedInNext[tmpPosition];
						}
					}

					if(lowerNode == 0){
						violatingLowHighFlag= true;
					}else{
						removeFromDerivedOutLowHigh(derivedY, derivedX);
						addToDerivedOutLowHigh(derivedY, lowerNode);

						if(derivedInLowHigh[derivedY][0] == 0){ // after removeFromDerivedOutLowHigh one of the two positions will be 0
							derivedInLowHigh[derivedY][0]= tmpNode;
							derivedInLowHighReversePosition[derivedY][0]= derivedOutLowHighCurrentPosition-1;
							derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= derivedY;
						}else{
							derivedInLowHigh[derivedY][1]= tmpNode;
							derivedInLowHighReversePosition[derivedY][1]= derivedOutLowHighCurrentPosition-1;
							derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= derivedY;
						}
					}
				}else{
					while(tmpPosition != 0){
						if(lowHighId[tmpNode] > lowHighId[derivedY] && inViolatingLowHigh[tmpNode] == false){
							higherNode= derivedInTarget[tmpPosition];
							break;
						}else{
							tmpPosition= derivedInNext[tmpPosition];
						}
					}

					if(higherNode == 0){
						violatingLowHighFlag= true;
					}else{
						removeFromDerivedOutLowHigh(derivedY, derivedX);
						addToDerivedOutLowHigh(derivedY, higherNode);

						if(derivedInLowHigh[derivedY][0] == 0){ // after removeFromDerivedOutLowHigh one of the two positions will be 0
							derivedInLowHigh[derivedY][0]= tmpNode;
							derivedInLowHighReversePosition[derivedY][0]= derivedOutLowHighCurrentPosition-1;
							derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= derivedY;
						}else{
							derivedInLowHigh[derivedY][1]= tmpNode;
							derivedInLowHighReversePosition[derivedY][1]= derivedOutLowHighCurrentPosition-1;
							derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= derivedY;
						}
					}
				}
			}else{ // deleted arc was from dominator
				while(tmpPosition != 0 && lowerNode == 0 && higherNode == 0){
					if(lowHighId[tmpNode] > lowHighId[derivedY] && inViolatingLowHigh[tmpNode] == false){
						higherNode= tmpNode;
					}else if(lowHighId[tmpNode] < lowHighId[derivedY] && inViolatingLowHigh[tmpNode] == false){
						lowerNode= tmpNode;
					}else{
						tmpPosition= derivedInNext[tmpPosition];
						tmpNode= derivedInTarget[tmpPosition];
					}
				}

				if(higherNode == 0 || lowerNode == 0){
					violatingLowHighFlag= true;
				}else{
					addToDerivedOutLowHigh(derivedY, lowerNode);
					addToDerivedOutLowHigh(derivedY, higherNode);
				}
			}
		}
	}

	return (returnValue);
}

void addToQList(int node){
	bool flag= false;
	int tmpPosition= r_First[node];
	while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
	int tmpNode= r_Target[tmpPosition];

	while(flag == false && tmpNode != 0){
		if(idom[node] == tmpNode){
			flag= true;
		}else{
			tmpPosition= r_Next[tmpPosition];
			while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
			tmpNode= r_Target[tmpPosition];
		}
	}

	if(flag == false && inQList[node] == 0){
		QList[nodesInQList]= node;
		inQList[node]= 1;
		nodesInQList++;
	}
}

void fixGrArcAfterInsertion(int graphArcPosition){
	if(correspondingGraphArc[correspondingDerivedArc[graphArcPosition]] == 0){
		correspondingGraphArc[correspondingDerivedArc[graphArcPosition]]= graphArcPosition;
	}else{
		int tmpPosition= correspondingGraphArc[correspondingDerivedArc[graphArcPosition]];

		correspondingGraphArc[correspondingDerivedArc[graphArcPosition]]= graphArcPosition;
		nextArcWithTheSameDerivedArc[graphArcPosition]= tmpPosition;
		prevArcWithTheSameDerivedArc[tmpPosition]= graphArcPosition;
	}
}

void fixGrArcAfterDeletion(int graphArcPosition){
	int nextPosition= nextArcWithTheSameDerivedArc[graphArcPosition];
	int prevPosition= prevArcWithTheSameDerivedArc[graphArcPosition];

	if(correspondingGraphArc[correspondingDerivedArc[graphArcPosition]] == graphArcPosition){
		correspondingGraphArc[correspondingDerivedArc[graphArcPosition]]= nextPosition;
		if(nextPosition != 0) prevArcWithTheSameDerivedArc[nextPosition]= 0;
		nextArcWithTheSameDerivedArc[graphArcPosition]= 0;
	}else{
		if(nextPosition != 0) prevArcWithTheSameDerivedArc[nextPosition]= prevPosition;
		if(prevPosition != 0) nextArcWithTheSameDerivedArc[prevPosition]= nextPosition;

		nextArcWithTheSameDerivedArc[graphArcPosition]= 0;
		prevArcWithTheSameDerivedArc[graphArcPosition]= 0;
	}
}

void checkIncomingEdges(int node){
	int tmpArcPosition= r_First[node];
	while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= r_Next[tmpArcPosition];
	int tmpArc= r_Target[tmpArcPosition];
	int currentArcPosition= 0;
	int currentArc= 0;
	int derivedX= 0;

	while(tmpArcPosition != 0){
		if(idom[tmpArc] != 0){ // no need to check incoming edges from unreachable nodes
			if(tmpArc == idom[node]){
				derivedArcFromDominator[node]= true;

				if(derivedInTarget[correspondingDerivedArc[tmpArcPosition]] != tmpArc){
					if(derivedInTarget[correspondingDerivedArc[tmpArcPosition]] != tmpArc || derivedOutTarget[correspondingDerivedArc[tmpArcPosition]] != node){
						if(removeFromDerivedGraph(correspondingDerivedArc[tmpArcPosition], false)){	
							derivedGraphInSiblings[node]--;
						}
						fixGrArcAfterDeletion(tmpArcPosition);
						
						correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(tmpArc, node);
						fixGrArcAfterInsertion(tmpArcPosition);
					}
				}else{
					if(prevLevel == level[derivedInTarget[correspondingDerivedArc[tmpArcPosition]]]){
						derivedGraphInSiblings[node]--;
					}
				}
			}else{
				derivedX= tmpArc;
				
				while(level[derivedX] != 1 && level[derivedX] != level[node]){
					derivedX= idom[derivedX];
				}

				if(derivedInTarget[correspondingDerivedArc[tmpArcPosition]] != derivedX || derivedOutTarget[correspondingDerivedArc[tmpArcPosition]] != node){
					if(correspondingDerivedArc[tmpArcPosition] != NULL){
						if(removeFromDerivedGraph(correspondingDerivedArc[tmpArcPosition], false)){
							derivedGraphInSiblings[node]--;
						}
						fixGrArcAfterDeletion(tmpArcPosition);
					}

					correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(derivedX, node);
					fixGrArcAfterInsertion(tmpArcPosition);
				}
			}
		}

		tmpArcPosition= r_Next[tmpArcPosition];
		while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= r_Next[tmpArcPosition];
		tmpArc= r_Target[tmpArcPosition];
	}

	if(insertionDeletionFlag == 1) prevIdom[node]= idom[node];
}

void addToViolatingLowHigh(int node){
	if(inViolatingLowHigh[node] == false){
		violatingLowHigh[violatingLowHighCounter]= node;
		positionInViolatingLowHigh[node]= violatingLowHighCounter;
		violatingLowHighCounter++;
		inViolatingLowHigh[node]= true;
	}
}

void addToNeedUpdateLowHigh(int node){
	inLowHighOrder[node]= false;

	if(inNeedUpdateLowHigh[node] == false){
		needUpdateLowHigh[needUpdateLowHighCounter]= node;
		inNeedUpdateLowHigh[node]= true;
		needUpdateLowHighCounter++;
	}
}

void updateLowHighIds(int node, int idomNode){
	int left= lowHighPrevNode[node];
	int right= lowHighNextNode[node];
	unsigned long long int minId= lowHighId[left];
	unsigned long long int maxId= lowHighId[right];
	int counter= 3; // left, node, right
	int level= 1;
	unsigned long long int idsBetweenNodes= 0;
	unsigned long long int nextId= 0;
	double overflowThreshold= 1/T;
	double density= 0.0;
	bool limitsFlag= false;

	if(left == 0) left= right;
	density= (double)((double)counter)/(maxId-minId+1);

	while(overflowThreshold <= density && limitsFlag == false){
		level++;

		if(minId != 0 && (minId%(1LL << level) != 0)){
			minId= minId-(minId%(1LL << level));
		}

		if(maxId <= ULLONG_MAX/4 && (maxId%(1LL << level) != (unsigned long long int)((1LL << level)-1))){
			maxId= minId+(1LL << level)-1;
		}

		if(maxId >= ULLONG_MAX/4) limitsFlag= true;

		while(lowHighPrevNode[left] != 0 && lowHighId[lowHighPrevNode[left]] >= minId){
			left= lowHighPrevNode[left];
			counter++;
		}

		while(lowHighNextNode[right] != 0 && lowHighId[lowHighNextNode[right]] <= maxId){
			right= lowHighNextNode[right];
			counter++;
		}

		density= (double)((double)counter)/(maxId-minId+1);
		overflowThreshold= overflowThreshold/T;
	}

	if(limitsFlag == true){
		maxId= ULLONG_MAX/4;
	}

	if(minId == 0){
		minId++;
		left= lowHighHead[idomNode];
	}else{
		if(lowHighId[left] < minId)left= lowHighNextNode[left];
	}

	lowHighId[left]= minId;
	idsBetweenNodes= (unsigned long long int)(1/density);
	nextId= minId+idsBetweenNodes;
	left= lowHighNextNode[left];

	while(left != right){
		lowHighId[left]= nextId;
		nextId+= idsBetweenNodes;
		left= lowHighNextNode[left];
	}

	if(lowHighId[right] < maxId) lowHighId[right]= nextId;
}

void giveNodeLowHighId(int node, int left, int right){
	if(!(left == 0 && right == 0) && lowHighId[right]-lowHighId[left] == 1){
		updateLowHighIds(node, idom[node]);
	}else if(left == 0 && right == 0){
		lowHighId[node]= ULLONG_MAX/4;
	}else if(left == 0){
		lowHighId[node]= lowHighId[right]/2;	
	}else{
		lowHighId[node]= lowHighId[left]+(lowHighId[right]-lowHighId[left])/2;
	}
}

void quickSortSiblingsInLowHighOrder(int left, int right){
   int i, j, pivot, temp;

   if(left< right){
      pivot= left;
      i= left;
      j= right;

      while(i< j){
         while(lowHighId[siblingsInLowHighOrder[i]] <= lowHighId[siblingsInLowHighOrder[pivot]] && i< right) i++;
         while(lowHighId[siblingsInLowHighOrder[j]] > lowHighId[siblingsInLowHighOrder[pivot]]) j--;
            
         if(i< j){
            temp= siblingsInLowHighOrder[i];
            siblingsInLowHighOrder[i]= siblingsInLowHighOrder[j];
            siblingsInLowHighOrder[j]= temp;
         }
      }

      temp= siblingsInLowHighOrder[pivot];
      siblingsInLowHighOrder[pivot]= siblingsInLowHighOrder[j];
      siblingsInLowHighOrder[j]= temp;
      quickSortSiblingsInLowHighOrder(left, j-1);
      quickSortSiblingsInLowHighOrder(j+1, right);
   }
}

void addChildToLowHigh(int node, int idomNode){
	int derivedArcLeft= 0;
	int derivedArcRight= 0;
	int dominator= 0;
	int tmpPosition= 0;
	int tmpNode= 0;
	int left= 0;
	int right= 0;
	bool derivedArcFromIdom= false;

	siblingsInLowHighOrderCounter= 0;

	tmpPosition= derivedInFirst[node];
	tmpNode= derivedInTarget[tmpPosition];

	while(tmpPosition != 0){
		if(tmpNode == idom[node]){
			derivedArcFromIdom= true;
			derivedArcFromDominator[node]= true;
		}else if(inLowHighOrder[tmpNode] == true){
			siblingsInLowHighOrder[siblingsInLowHighOrderCounter]= tmpNode;
			siblingsInLowHighOrderCounter++;
		}

		tmpPosition= derivedInNext[tmpPosition];
		tmpNode= derivedInTarget[tmpPosition];
	}

	siblingsInLowHighOrder[siblingsInLowHighOrderCounter]= 0;
	dominator= idom[node];

	if(derivedArcFromIdom == true){
		if(lowHighHead[dominator] == 0){
			lowHighHead[dominator]= node;
			giveNodeLowHighId(node, 0, 0);
		}else if(siblingsInLowHighOrderCounter == 0){
			lowHighPrevNode[lowHighHead[dominator]]= node;
			lowHighNextNode[node]= lowHighHead[dominator];
			lowHighHead[dominator]= node;
			giveNodeLowHighId(node, 0, lowHighNextNode[node]);
		}else if(siblingsInLowHighOrderCounter == 1){ // only two derived arcs (one of them from dominator)
			lowHighPrevNode[lowHighHead[dominator]]= node;
			lowHighNextNode[node]= lowHighHead[dominator];
			lowHighHead[dominator]= node;
			giveNodeLowHighId(node, 0, lowHighNextNode[node]);
		}else{ // at least 2 derived arcs
			quickSortSiblingsInLowHighOrder(0, siblingsInLowHighOrderCounter-1);
			left= (siblingsInLowHighOrderCounter-1)/2;
			right= left+1;
			derivedArcLeft= siblingsInLowHighOrder[left];
			derivedArcRight= lowHighNextNode[derivedArcLeft];
					
			lowHighNextNode[derivedArcLeft]= node;
			lowHighPrevNode[node]= derivedArcLeft;
			lowHighPrevNode[derivedArcRight]= node;
			lowHighNextNode[node]= derivedArcRight;
			giveNodeLowHighId(node, lowHighPrevNode[node], lowHighNextNode[node]);
		}

		derivedInLowHigh[node][0]= idom[node];
		derivedInLowHigh[node][1]= idom[node];
	}else{ // at least 2 derived arcs
		quickSortSiblingsInLowHighOrder(0, siblingsInLowHighOrderCounter-1);

		left= (siblingsInLowHighOrderCounter-1)/2;
		right= left+1;
		derivedArcLeft= siblingsInLowHighOrder[left];
		derivedArcRight= lowHighNextNode[derivedArcLeft];

		lowHighNextNode[derivedArcLeft]= node;
		lowHighPrevNode[node]= derivedArcLeft;
		lowHighPrevNode[derivedArcRight]= node;
		lowHighNextNode[node]= derivedArcRight;
		giveNodeLowHighId(node, lowHighPrevNode[node], lowHighNextNode[node]);
				
		addToDerivedOutLowHigh(node, siblingsInLowHighOrder[left]);
		derivedInLowHigh[node][0]= siblingsInLowHighOrder[left];
		derivedInLowHighReversePosition[node][0]= derivedOutLowHighCurrentPosition-1;
		derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= node;

		addToDerivedOutLowHigh(node, siblingsInLowHighOrder[right]);
		derivedInLowHigh[node][1]= siblingsInLowHighOrder[right];
		derivedInLowHighReversePosition[node][1]= derivedOutLowHighCurrentPosition-1;
		derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= node;
	}

	inLowHighChildrenList[node]= true;
}

bool removeChildFromLowHigh(int node, int idomNode){
	int leftNode= lowHighPrevNode[node];
	int rightNode= lowHighNextNode[node];
	bool returnValue= false;

	if(inLowHighChildrenList[node] == true){
		if(leftNode != 0){
			lowHighNextNode[leftNode]= lowHighNextNode[node];
		}else{
			lowHighHead[idomNode]= lowHighNextNode[node];
		}

		if(rightNode != 0){
			lowHighPrevNode[rightNode]= lowHighPrevNode[node];
		}

		lowHighPrevNode[node]= 0;
		lowHighNextNode[node]= 0;

		if(derivedInLowHigh[node][0] != derivedInLowHigh[node][1]){
			removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][0]);
			removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][1]);
		}

		derivedArcFromDominator[node]= false;
		inLowHighChildrenList[node]= false;

		returnValue= true;
	}

	return(returnValue);
}

void removeFromViolatingLowHigh(int node){
	int position= positionInViolatingLowHigh[node];
	int lastInViolatingLowHigh= violatingLowHigh[violatingLowHighCounter-1];

	violatingLowHigh[position]= lastInViolatingLowHigh;	
	positionInViolatingLowHigh[lastInViolatingLowHigh]= position;
	violatingLowHigh[violatingLowHighCounter-1]= 0;
	violatingLowHighCounter--;
	positionInViolatingLowHigh[node]= 0;
	inViolatingLowHigh[node]= false;
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void updateInSiblings(int w, int c, int lowHighDominator, int mode){
	int qPosition= derivedOutFirst[w];
	int q= derivedOutTarget[qPosition];
	bool qBelongsDerivedOutC= false;

	while(q != 0){
		int qNextPosition= derivedOutNext[qPosition];
		
		qBelongsDerivedOutC= false;

		if(derivedOutArcsCounter[c] < derivedInArcsCounter[q]){
			int tmpDerivedOutPositionC= derivedOutFirst[c];
			int tmpDerivedOutC= derivedOutTarget[tmpDerivedOutPositionC];

			while(qBelongsDerivedOutC == false && tmpDerivedOutC != 0){
				if(tmpDerivedOutC == q){
					qBelongsDerivedOutC= true;
				}else{
					tmpDerivedOutPositionC= derivedOutNext[tmpDerivedOutPositionC];
					tmpDerivedOutC= derivedOutTarget[tmpDerivedOutPositionC];
				}
			}
		}else{
			int tmpDerivedInPositionQ= derivedInFirst[q];
			int tmpDerivedInQ= derivedInTarget[tmpDerivedInPositionQ];

			while(qBelongsDerivedOutC == false && tmpDerivedInQ != 0){
				if(tmpDerivedInQ == c){
					qBelongsDerivedOutC= true;
				}else{
					tmpDerivedInPositionQ= derivedInNext[tmpDerivedInPositionQ];
					tmpDerivedInQ= derivedInTarget[tmpDerivedInPositionQ];
				}
			}
		}

		if(qBelongsDerivedOutC == true){
			derivedGraphInSiblings[q]--;
			if(derivedGraphInSiblings[q] == 1){
				addToQList(q);

				if(inViolatingLowHigh[q] == true && inQList[q] == 1){
					removeFromViolatingLowHigh(q);
				}else if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
					addToViolatingLowHigh(q);
				}
			}else{
				if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
					addToViolatingLowHigh(q);
				}
			}

			int tmpArcPosition= correspondingGraphArc[qPosition];
			while(!(removeFromDerivedGraph(qPosition, false))){
				fixGrArcAfterDeletion(tmpArcPosition);
				correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(c, q);
				fixGrArcAfterInsertion(tmpArcPosition);
				tmpArcPosition= correspondingGraphArc[qPosition];				
			}
			if(qNextPosition == derivedGraphCurrentPosition) qNextPosition= qPosition; // derived arc changed position

			correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(c, q);
			fixGrArcAfterInsertion(tmpArcPosition);
			tmpArcPosition= correspondingGraphArc[qPosition];
		}else{
			if(prevLevel == level[q]){
				derivedGraphInSiblings[q]--;

				int tmpArcPosition= correspondingGraphArc[qPosition];
				while(!(removeFromDerivedGraph(qPosition, false))){
					fixGrArcAfterDeletion(tmpArcPosition);
					correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(c, q);
					fixGrArcAfterInsertion(tmpArcPosition);
					tmpArcPosition= correspondingGraphArc[qPosition];
				}
				if(qNextPosition == derivedGraphCurrentPosition) qNextPosition= qPosition; // derived arc changed position

				correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(c, q);
				fixGrArcAfterInsertion(tmpArcPosition);
			}

			if((derivedInLowHigh[q][0] == w || derivedInLowHigh[q][1] == w) && idom[q] == lowHighDominator){
				addToViolatingLowHigh(q);
			}
		}
		
		qPosition= qNextPosition;
		q= derivedOutTarget[qPosition];
	}

	if(mode == 0){
		bool removeChildFromLowHighFlag= removeChildFromLowHigh(w, prevIdom[w]);
		if(removeChildFromLowHighFlag == true) addChildToLowHigh(w, idom[w]);
		inLowHighOrder[w]= true;
	}

	prevIdom[w]= idom[w];
}

void dfsDominator(int node){
	int position, selectedNode;

	dfsDominatorDiscovered[node]= 1;
	createPreorderList(node);
	preorder2labelDominator[node]= dfsDominatorCounter;
	label2preorderDominator[dfsDominatorCounter++]= node;

	position= dominatorFirst[node];
	while(position != 0){
		selectedNode= dominatorTarget[position];

		if(dfsDominatorDiscovered[selectedNode] == 1){
			position= dominatorNext[position];
			continue;
		}else{
			dfsDominator(selectedNode);
			createPostorderList(selectedNode);
			size[node]+= size[selectedNode];
		}
	}

	if(node == r) createPostorderList(node);
}

void initializeDominatorTreeStructures(){
	int nodes= n+1;
	int currentPosition= 1;

	// calculate dominator tree from idom's
	for(int i= 1; i <= nodes; i++){
		if(idom[i] != i && idom[i] != 0){ // except the root of dominator tree and unreachable nodes
			if(dominatorFirst[idom[i]] == 0){
				dominatorTarget[currentPosition]= i;
				dominatorFirst[idom[i]]= currentPosition++;
			}else{
				dominatorTarget[currentPosition]= i;
				dominatorNext[currentPosition]= dominatorFirst[idom[i]];
				dominatorFirst[idom[i]]= currentPosition++;
			}
		}
	}

	dfsDominator(r);
}

// 0 -> preorder
// 1 -> postorder
void cutMovingNodes(struct node* left, struct node* right, struct node* movingLeft, struct node* movingRight, int mode){
	struct representative* leftRepresentative= NULL;
	struct representative* rightRepresentative= NULL;

	if(mode == 0){ // preorder
		if(left->rep == movingLeft->rep) splitRepresentative(left, movingLeft, 0);
		if(right != NULL && right->rep == movingRight->rep) splitRepresentative(movingRight, right, 0);

		leftRepresentative= left->rep;
		if(right != NULL) rightRepresentative= right->rep;

		if(right != NULL){	
			if(leftRepresentative != rightRepresentative){
				leftRepresentative->rightRepresentative->leftRepresentative= NULL;
				rightRepresentative->leftRepresentative->rightRepresentative= NULL;
				leftRepresentative->rightRepresentative= rightRepresentative;
				rightRepresentative->leftRepresentative= leftRepresentative;
			}
		}else{
			leftRepresentative->rightRepresentative->leftRepresentative= NULL;
			leftRepresentative->rightRepresentative=  NULL;
		}
	}else{ //postorder
		if(left != NULL && left->rep == movingLeft->rep)	 splitRepresentative(left, movingLeft, 1);
		if(right->rep == movingRight->rep) splitRepresentative(movingRight, right, 1);

		if(left != NULL) leftRepresentative= left->rep;
		rightRepresentative= right->rep;

		if(left != NULL){
			if(leftRepresentative != rightRepresentative){
				leftRepresentative->rightRepresentative->leftRepresentative= NULL;
				rightRepresentative->leftRepresentative->rightRepresentative= NULL;
				leftRepresentative->rightRepresentative= rightRepresentative;
				rightRepresentative->leftRepresentative= leftRepresentative;
			}
		}else{
			rightRepresentative->leftRepresentative->rightRepresentative= NULL;
			rightRepresentative->leftRepresentative= NULL;
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void updateIds(int x, int y, int mode, int prevLevelX){ // y is the new idom of x (idom[x] == y)
	node* leftNodePreorder= NULL; // aristeros komvos apo tous komvous pou tha metakinithoun
	node* rightNodePreorder= NULL; // dexios komvos apo tous komvous pou tha metakinithoun
	node* movingLeftNodePreorder= NULL; // aristeroteros komvos apo autous pou tha metakinithoun
	node* movingRightNodePreorder= NULL; // dexios komvos apo autous pou tha metakinithoun
	node* newLeftNodePreorder= NULL;
	node* newRightNodePreorder= NULL;

	representative* leftRepresentativePreorder= NULL; // aristeros antiproswpos apo tous komvous pou tha metakinithoun
	representative* rightRepresentativePreorder= NULL; // dexios antiproswpos apo tous komvous pou tha metakinithoun
	representative* movingLeftRepresentativePreorder= NULL; // aristeroteros antiproswpos apo autous pou tha metakinithoun
	representative* movingRightRepresentativePreorder= NULL; // dexios antiproswpos apo autous pou tha metakinithoun
	representative* newLeftRepresentativePreorder= NULL; // aristeroteros antiproswpos ths neas theshs twn komvwn
	representative* newRightRepresentativePreorder= NULL; // dexios antiproswpos ths neas theshs twn komvwn

	node* leftNodePostorder= NULL;
	node* rightNodePostorder= NULL;
	node* movingLeftNodePostorder= NULL;
	node* movingRightNodePostorder= NULL;
	node* newLeftNodePostorder= NULL;
	node* newRightNodePostorder= NULL;

	representative* leftRepresentativePostorder= NULL;
	representative* rightRepresentativePostorder= NULL;
	representative* movingLeftRepresentativePostorder= NULL;
	representative* movingRightRepresentativePostorder= NULL;
	representative* newLeftRepresentativePostorder= NULL;
	representative* newRightRepresentativePostorder= NULL;

	representative* tmpRepresentative= NULL;	
	node* tmpNode= NULL;

	int representativesCounterPreorder= 0;
	int representativesCounterPostorder= 0;
	int currentLevel= 0;

	unsigned long long int idDifferencePreorder= 0;
	unsigned long long int idDifferencePostorder= 0;
	unsigned long long int idsBetweenNodes= 0;
	unsigned long long int nextId= 0;

	bool preorderFlag= false;
	bool postorderFlag= false;
	bool preorderNodeFound= false;
	bool postorderNodeFound= false;

	if(y == -1){ // node x became unreachable (deletions)
		// we traverse preorder bottom lists so we can update idom, level, derivedGraphInSiblings 
		// preorder
		leftNodePreorder= nodesTablePreorder[x]->leftNode;
		if(leftNodePreorder == NULL) leftNodePreorder= nodesTablePreorder[x]->rep->leftRepresentative->nodesListTail;
		
		rightNodePreorder= nodesTablePreorder[x]->rightNode;
		if(rightNodePreorder == NULL && nodesTablePreorder[x]->rep->rightRepresentative != NULL){
			rightNodePreorder= nodesTablePreorder[x]->rep->rightRepresentative->nodesListHead;
		}

		movingLeftNodePostorder= nodesTablePreorder[x];
		int tmpLevel= 0;

		while(rightNodePreorder != NULL){
			if(level[rightNodePreorder->nodesName] > prevLevel){
				if(postorderNodeFound == false && level[rightNodePreorder->nodesName] > tmpLevel){
					movingLeftNodePostorder= rightNodePreorder;
					tmpLevel= level[movingLeftNodePostorder->nodesName];
				}else{
					postorderNodeFound= true;
				}

				idom[rightNodePreorder->nodesName]= 0;
				if(mode == 0) removeChildFromLowHigh(rightNodePreorder->nodesName, prevIdom[rightNodePreorder->nodesName]);
				prevIdom[rightNodePreorder->nodesName]= 0;
				level[rightNodePreorder->nodesName]= 0;
				derivedGraphInSiblings[rightNodePreorder->nodesName]= 0;

				if(rightNodePreorder->rightNode != NULL){
					rightNodePreorder= rightNodePreorder->rightNode;
				}else if(rightNodePreorder->rep->rightRepresentative != NULL){
					rightNodePreorder= rightNodePreorder->rep->rightRepresentative->nodesListHead;
				}else{
					rightNodePreorder= NULL;
				}
			}else{
				break;
			}
		}

		movingLeftNodePostorder= nodesTablePostorder[movingLeftNodePostorder->nodesName];

		// exw leftNodePreorder - rightNodePreorder (mporei na einai NULL)
		leftRepresentativePreorder= leftNodePreorder->rep;
		(rightNodePreorder != NULL) ? rightRepresentativePreorder= rightNodePreorder->rep : rightRepresentativePreorder= NULL;

		if(rightRepresentativePreorder == NULL){
			leftNodePreorder->rightNode= NULL;
			leftRepresentativePreorder->nodesListTail= leftNodePreorder;
			leftRepresentativePreorder->rightRepresentative= NULL;

			leftRepresentativePreorder->leaves= 0;
			for(node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;
		}else if(leftRepresentativePreorder == rightRepresentativePreorder){
			leftNodePreorder->rightNode= rightNodePreorder;
			rightNodePreorder->leftNode= leftNodePreorder;

			leftRepresentativePreorder->leaves= 0;
			for(node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;
		}else{ // leftRepresentativePreorder != rightRepresentativePreorder
			leftRepresentativePreorder->rightRepresentative= rightRepresentativePreorder;
			rightRepresentativePreorder->leftRepresentative= leftRepresentativePreorder;

			leftNodePreorder->rightNode= NULL;
			leftRepresentativePreorder->nodesListTail= leftNodePreorder;
			rightNodePreorder->leftNode= NULL;
			rightRepresentativePreorder->nodesListHead= rightNodePreorder;
			rightRepresentativePreorder->representativesName= rightNodePreorder->nodesName;

			leftRepresentativePreorder->leaves= 0;
			for(node* tmpNode= leftRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePreorder->leaves++;

			rightRepresentativePreorder->leaves= 0;
			for(node* tmpNode= rightRepresentativePreorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePreorder->leaves++;

			if(leftRepresentativePreorder->leaves+rightRepresentativePreorder->leaves < nodesPerRepresentative) mergeRepresentatives(leftRepresentativePreorder, rightRepresentativePreorder);
		}

		// postorder
		rightNodePostorder= nodesTablePostorder[x]->rightNode;
		if(rightNodePostorder == NULL) rightNodePostorder= nodesTablePostorder[x]->rep->rightRepresentative->nodesListHead;

		leftNodePostorder= movingLeftNodePostorder->leftNode;
		if(leftNodePostorder == NULL && movingLeftNodePostorder->rep->leftRepresentative != NULL) leftNodePostorder= movingLeftNodePostorder->rep->leftRepresentative->nodesListTail;

		rightRepresentativePostorder= rightNodePostorder->rep;
		(leftNodePostorder != NULL) ? leftRepresentativePostorder= leftNodePostorder->rep : leftRepresentativePostorder= NULL;

		if(leftRepresentativePostorder == NULL){
			rightNodePostorder->leftNode= NULL;
			rightRepresentativePostorder->nodesListHead= rightNodePostorder;
			rightRepresentativePostorder->representativesName= rightNodePostorder->nodesName;
			rightRepresentativePostorder->leftRepresentative= NULL;

			rightRepresentativePostorder->leaves= 0;
			for(node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;
		}else if(leftRepresentativePostorder == rightRepresentativePostorder){
			rightNodePostorder->leftNode= leftNodePostorder;
			leftNodePostorder->rightNode= rightNodePostorder;

			rightRepresentativePostorder->leaves= 0;
			for(node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;
		}else{ // leftRepresentativePostorder != rightRepresentativePostorder
			leftRepresentativePostorder->rightRepresentative= rightRepresentativePostorder;
			rightRepresentativePostorder->leftRepresentative= leftRepresentativePostorder;

			leftNodePostorder->rightNode= NULL;
			leftRepresentativePostorder->nodesListTail= leftNodePostorder;
			rightNodePostorder->leftNode= NULL;
			rightRepresentativePostorder->nodesListHead= rightNodePostorder;
			rightRepresentativePostorder->representativesName= rightNodePostorder->nodesName;

			leftRepresentativePostorder->leaves= 0;
			for(node* tmpNode= leftRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) leftRepresentativePostorder->leaves++;

			rightRepresentativePostorder->leaves= 0;
			for(node* tmpNode= rightRepresentativePostorder->nodesListHead; tmpNode != NULL; tmpNode= tmpNode->rightNode) rightRepresentativePostorder->leaves++;

			if(leftRepresentativePostorder->leaves+rightRepresentativePostorder->leaves < nodesPerRepresentative) mergeRepresentatives(leftRepresentativePostorder, rightRepresentativePostorder);
		}
	}else{ // node x is still reachable (deletions + insertions)
		// preorder
		leftNodePreorder= nodesTablePreorder[x]->leftNode;
		if(leftNodePreorder == NULL) leftNodePreorder= nodesTablePreorder[x]->rep->leftRepresentative->nodesListTail;
		movingLeftNodePreorder= nodesTablePreorder[x];

		movingRightNodePreorder= nodesTablePostorder[x]; // we use postorder list to find movingRightNodePreorder

		tmpNode= movingRightNodePreorder->leftNode;
		if(tmpNode == NULL && movingRightNodePreorder->rep->leftRepresentative != NULL) tmpNode= movingRightNodePreorder->rep->leftRepresentative->nodesListTail;

		currentLevel= prevLevelX;
		while(tmpNode != NULL){
			if(level[tmpNode->nodesName] > currentLevel){
				movingRightNodePreorder= tmpNode;
				currentLevel= level[movingRightNodePreorder->nodesName];

				if(movingRightNodePreorder->leftNode != NULL){
					tmpNode= movingRightNodePreorder->leftNode;
				}else if(movingRightNodePreorder->rep->leftRepresentative != NULL){
					 tmpNode= movingRightNodePreorder->rep->leftRepresentative->nodesListTail;
				}else{
					tmpNode= NULL;
				}
			}else{
				break;
			}
		}

		movingRightNodePreorder= nodesTablePreorder[movingRightNodePreorder->nodesName]; // movingRightNodePreorder was pointer to postorder node
		rightNodePreorder= movingRightNodePreorder->rightNode;
		if(rightNodePreorder == NULL && movingRightNodePreorder->rep->rightRepresentative != NULL) rightNodePreorder= movingRightNodePreorder->rep->rightRepresentative->nodesListHead;

		leftRepresentativePreorder= leftNodePreorder->rep;
		(rightNodePreorder != NULL) ? rightRepresentativePreorder= rightNodePreorder->rep : rightRepresentativePreorder= NULL;
		
		cutMovingNodes(leftNodePreorder, rightNodePreorder, movingLeftNodePreorder, movingRightNodePreorder, 0);
		movingLeftRepresentativePreorder= movingLeftNodePreorder->rep;
		movingRightRepresentativePreorder= movingRightNodePreorder->rep;

		representativesCounterPreorder= 1;
		tmpRepresentative= movingLeftRepresentativePreorder;
		while(tmpRepresentative != movingRightRepresentativePreorder){
			representativesCounterPreorder++;
			tmpRepresentative= tmpRepresentative->rightRepresentative;
		}

		// postorder
		rightNodePostorder= nodesTablePostorder[x]->rightNode;
		if(rightNodePostorder == NULL) rightNodePostorder= nodesTablePostorder[x]->rep->rightRepresentative->nodesListHead;
		movingRightNodePostorder= nodesTablePostorder[x];

		movingLeftNodePostorder= nodesTablePreorder[x];  // we use postorder list to find movingRightNodePreorder

		tmpNode= movingLeftNodePostorder->rightNode;
		if(tmpNode == NULL && movingLeftNodePostorder->rep->rightRepresentative != NULL) tmpNode= movingLeftNodePostorder->rep->rightRepresentative->nodesListHead;

		currentLevel= prevLevelX;
		while(tmpNode != NULL){
			if(level[tmpNode->nodesName] > currentLevel){
				movingLeftNodePostorder= tmpNode;
				currentLevel= level[movingLeftNodePostorder->nodesName];

				if(movingLeftNodePostorder->rightNode != NULL){
					tmpNode= movingLeftNodePostorder->rightNode;
				}else if(movingLeftNodePostorder->rep->rightRepresentative != NULL){
					 tmpNode= movingLeftNodePostorder->rep->rightRepresentative->nodesListHead;
				}else{
					tmpNode= NULL;
				}
			}else{
				break;
			}
		}

		movingLeftNodePostorder= nodesTablePostorder[movingLeftNodePostorder->nodesName]; // movingLeftNodePostorder was pointer to postorder node
		leftNodePostorder= movingLeftNodePostorder->leftNode;
		if(leftNodePostorder == NULL && movingLeftNodePostorder->rep->leftRepresentative != NULL) leftNodePostorder= movingLeftNodePostorder->rep->leftRepresentative->nodesListTail;

		(leftNodePostorder != NULL) ? leftRepresentativePostorder= leftNodePostorder->rep : leftRepresentativePostorder= NULL;
		rightRepresentativePostorder= rightNodePostorder->rep;
		
		cutMovingNodes(leftNodePostorder, rightNodePostorder, movingLeftNodePostorder, movingRightNodePostorder, 1);
		movingLeftRepresentativePostorder= movingLeftNodePostorder->rep;
		movingRightRepresentativePostorder= movingRightNodePostorder->rep; 

		representativesCounterPostorder= 1;
		tmpRepresentative= movingLeftRepresentativePostorder;
		while(tmpRepresentative != movingRightRepresentativePostorder){
			representativesCounterPostorder++;
			tmpRepresentative= tmpRepresentative->rightRepresentative;
		}

		// move nodes to their new position
		// preorder
		newLeftRepresentativePreorder= nodesTablePreorder[y]->rep;
		newRightRepresentativePreorder= NULL;

		if(newLeftRepresentativePreorder->nodesListTail->nodesName == y){
			newRightRepresentativePreorder= newLeftRepresentativePreorder->rightRepresentative;
		}else{
			newLeftNodePreorder= nodesTablePreorder[y];
			newRightNodePreorder= newLeftNodePreorder->rightNode;

			splitRepresentative(newLeftNodePreorder, newRightNodePreorder, 0);
			if(newLeftNodePreorder->rep == leftNodePreorder->rep->leftRepresentative && movingLeftNodePreorder->rep->tag - newLeftNodePreorder->rep->tag != 1){
				newRightNodePreorder->rep->tag= newLeftNodePreorder->rep->tag + ((movingLeftNodePreorder->rep->tag - newLeftNodePreorder->rep->tag)/2);
			}

			newRightRepresentativePreorder= newRightNodePreorder->rep;
		}

		// postorder
		newRightNodePostorder= nodesTablePreorder[y];
		if(newRightNodePostorder == NULL){
			if(nodesTablePreorder[y]->rep->rightRepresentative == NULL){
				newRightNodePostorder= nodesTablePreorder[y];
			}else{
				newRightNodePostorder= nodesTablePreorder[y]->rep->rightRepresentative->nodesListHead;
			}
		}

		tmpNode= newRightNodePostorder->rightNode;
		if(tmpNode == NULL && newRightNodePostorder->rep->rightRepresentative != NULL) tmpNode= newRightNodePostorder->rep->rightRepresentative->nodesListHead;
	
		while(tmpNode != NULL){
			if(level[tmpNode->nodesName] > level[newRightNodePostorder->nodesName]){
				newRightNodePostorder= tmpNode;

				if(newRightNodePostorder->rightNode != NULL){
					tmpNode= newRightNodePostorder->rightNode;
				}else if(newRightNodePostorder->rep->rightRepresentative != NULL){
					 tmpNode= newRightNodePostorder->rep->rightRepresentative->nodesListHead;
				}else{
					tmpNode= NULL;
				}
			}else{
				break;
			}
		}

		newRightNodePostorder= nodesTablePostorder[newRightNodePostorder->nodesName]; // newRightNodePostorder was pointer to a preorder node
		newRightRepresentativePostorder= newRightNodePostorder->rep;
	
		newLeftNodePostorder= newRightNodePostorder->leftNode;
		if(newLeftNodePostorder == NULL && newRightNodePostorder->rep->leftRepresentative != NULL) newLeftNodePostorder= newRightNodePostorder->rep->leftRepresentative->nodesListTail;
		if(newLeftNodePostorder != NULL) newLeftRepresentativePostorder= newLeftNodePostorder->rep;

		if(newLeftNodePostorder != NULL){
			if(newLeftNodePostorder->rep != newRightNodePostorder->rep){
				newRightRepresentativePostorder= newLeftRepresentativePostorder->rightRepresentative;
			}else{
				splitRepresentative(newLeftNodePostorder, newRightNodePostorder, 1);
				newRightRepresentativePostorder= newRightNodePostorder->rep;
			}
		}else{
			newLeftRepresentativePostorder= NULL;
		}

		// preorder
		if(newRightRepresentativePreorder == NULL){
			idDifferencePreorder= ULLONG_MAX/4 - newLeftRepresentativePreorder->tag;
		}else{
			idDifferencePreorder= newRightRepresentativePreorder->tag - newLeftRepresentativePreorder->tag;
		}

		if(idDifferencePreorder <= representativesCounterPreorder){
			relabelRepresentatives(y, 0, representativesCounterPreorder);

			if(newRightRepresentativePreorder == NULL){
				idDifferencePreorder= ULLONG_MAX/4 - newLeftRepresentativePreorder->tag;
			}else{
				idDifferencePreorder= newRightRepresentativePreorder->tag - newLeftRepresentativePreorder->tag;
			}
		}

		if(newRightRepresentativePreorder == NULL){
			newLeftRepresentativePreorder->rightRepresentative= movingLeftRepresentativePreorder;
			movingLeftRepresentativePreorder->leftRepresentative= newLeftRepresentativePreorder;

			movingRightRepresentativePreorder->rightRepresentative= NULL;
		}else{
			preorderFlag= true;

			newLeftRepresentativePreorder->rightRepresentative= movingLeftRepresentativePreorder;
			movingLeftRepresentativePreorder->leftRepresentative= newLeftRepresentativePreorder;

			newRightRepresentativePreorder->leftRepresentative= movingRightRepresentativePreorder;
			movingRightRepresentativePreorder->rightRepresentative= newRightRepresentativePreorder;
		}

		// postorder
		if(newLeftRepresentativePostorder == NULL){
			idDifferencePostorder= newRightRepresentativePostorder->tag;
		}else{
			idDifferencePostorder= newRightRepresentativePostorder->tag - newLeftRepresentativePostorder->tag;
		}

		if(idDifferencePostorder <= representativesCounterPostorder){
			relabelRepresentatives(newRightNodePostorder->nodesName, 1, representativesCounterPostorder);

			if(newLeftRepresentativePostorder == NULL){
				idDifferencePostorder= newRightRepresentativePostorder->tag;
			}else{
				idDifferencePostorder= newRightRepresentativePostorder->tag - newLeftRepresentativePostorder->tag;
			}
		}

		if(newLeftRepresentativePostorder == NULL){
			newRightRepresentativePostorder->leftRepresentative= movingRightRepresentativePostorder;
			movingRightRepresentativePostorder->rightRepresentative= newRightRepresentativePostorder;

			movingLeftRepresentativePostorder->leftRepresentative= NULL;
		}else{
			postorderFlag= true;

			newRightRepresentativePostorder->leftRepresentative= movingRightRepresentativePostorder;
			movingRightRepresentativePostorder->rightRepresentative= newRightRepresentativePostorder;

			newLeftRepresentativePostorder->rightRepresentative=movingLeftRepresentativePostorder;
			movingLeftRepresentativePostorder->leftRepresentative= newLeftRepresentativePostorder;
		}

		// preorder
		tmpRepresentative= movingLeftRepresentativePreorder;
		representativesCounterPreorder++;

		if(representativesCounterPreorder == 1){
			idsBetweenNodes= idDifferencePreorder/representativesCounterPreorder;
			tmpRepresentative->tag= newLeftRepresentativePreorder->tag + idsBetweenNodes;
		}else{
			idsBetweenNodes= idDifferencePreorder/representativesCounterPreorder;
			nextId= newLeftRepresentativePreorder->tag + idsBetweenNodes;

			while(tmpRepresentative != NULL && tmpRepresentative != newRightRepresentativePreorder){
				tmpRepresentative->tag= nextId;
				nextId+= idsBetweenNodes;
				tmpRepresentative= tmpRepresentative->rightRepresentative;
			}
		}

		// postorder
		tmpRepresentative= movingRightRepresentativePostorder;
		representativesCounterPostorder++;

		if(representativesCounterPostorder == 1){
			idsBetweenNodes= idDifferencePostorder/representativesCounterPostorder;
			tmpRepresentative->tag= newRightRepresentativePostorder->tag - idsBetweenNodes;
		}else{
			idsBetweenNodes= idDifferencePostorder/representativesCounterPostorder;
			nextId= newRightRepresentativePostorder->tag - idsBetweenNodes;

			while(tmpRepresentative != NULL && tmpRepresentative != newLeftRepresentativePostorder){
				tmpRepresentative->tag= nextId;
				nextId-= idsBetweenNodes;
				tmpRepresentative= tmpRepresentative->leftRepresentative;
			}
		}

		// merge if needed
		// preorder
		if(preorderFlag == true){
			if(newLeftRepresentativePreorder->leaves+movingLeftRepresentativePreorder->leaves < nodesPerRepresentative){
				mergeRepresentatives(newLeftRepresentativePreorder, movingLeftRepresentativePreorder);
				if(movingRightRepresentativePreorder == movingLeftRepresentativePreorder) movingRightRepresentativePreorder= newLeftRepresentativePreorder;
			}
			if(newRightRepresentativePreorder->leaves+movingRightRepresentativePreorder->leaves < nodesPerRepresentative) mergeRepresentatives(movingRightRepresentativePreorder, newRightRepresentativePreorder);
		}

		// postorder
		if(postorderFlag == true){
			if(newLeftRepresentativePostorder->leaves+movingLeftRepresentativePostorder->leaves < nodesPerRepresentative){
				mergeRepresentatives(newLeftRepresentativePostorder, movingLeftRepresentativePostorder);
				if(movingRightRepresentativePostorder == movingLeftRepresentativePostorder) movingRightRepresentativePostorder= newLeftRepresentativePostorder;
			}
			if(newRightRepresentativePostorder->leaves+movingRightRepresentativePostorder->leaves < nodesPerRepresentative) mergeRepresentatives(movingRightRepresentativePostorder, newRightRepresentativePostorder);
		}
	}
}

void updateDominatorTreeLevels(int node){
	struct node* tmpNode= nodesTablePreorder[node]->rightNode;
	struct representative* tmpRep= NULL;

	if(tmpNode == NULL){
		if(nodesTablePreorder[node]->rep->rightRepresentative == NULL){
			tmpNode= NULL;
		}else{
			tmpRep= nodesTablePreorder[node]->rep->rightRepresentative;
			tmpNode= tmpRep->nodesListHead;
		}
	}

	while(tmpNode != NULL && isChild(node, tmpNode->nodesName)){
		level[tmpNode->nodesName]= level[idom[tmpNode->nodesName]]+1;

		if(tmpNode->rightNode != NULL){
			tmpNode= tmpNode->rightNode;
		}else{
			tmpRep= tmpNode->rep->rightRepresentative;
			
			if(tmpRep == NULL){
				break;
			}else{
				tmpNode= tmpRep->nodesListHead;
			}
		}
	}
}

void fixDerivedArcFromDominator(int node){
	int tmpPosition= derivedInFirst[node];
	int tmpNode= derivedInTarget[tmpPosition];

	while(tmpNode != 0){
		if(tmpNode == idom[node]){
			derivedArcFromDominator[node]= true;

			if(derivedInLowHigh[node][0] != derivedInLowHigh[node][1]){
				removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][0]);
				removeFromDerivedOutLowHigh(node, derivedInLowHigh[node][1]);
			}

			derivedInLowHigh[node][0]= idom[node];
			derivedInLowHigh[node][1]= idom[node];
			return;
		}

		tmpPosition= derivedInNext[tmpPosition];
		tmpNode= derivedInTarget[tmpPosition];
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void locateNewParent(int w, int c, int y, int mode){
	int u= 0;
	int tmpArcPosition= 0;
	int tmpArc= 0;

	noNewParentFlag= false;

	// D'[c,d'(y)]
	if(criticalPathFlag == false){
		int tmp= idom[y];

		while(tmp != idom[c]){
			criticalPathCounter++;
			tmp= idom[tmp];
		}

		tmp= y;
		while(criticalPathCounter != -1){
			criticalPath[criticalPathCounter]= tmp;
			criticalPathCounter--;
			tmp= idom[tmp];
		}
		criticalPathFlag= true;
		criticalPathCounter= 0;
	}

	u= criticalPath[criticalPathCounter];

	while(u != 0){
		if(c != idom[y]){
			tmpArcPosition= r_First[w];
			while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= r_Next[tmpArcPosition];
			tmpArc= r_Target[tmpArcPosition];

			while(tmpArcPosition != 0){
				if(!isChild(u ,tmpArc)){
					if(idom[w] != idom[u] && idom[w] != tmpArc){
						idom[w]= idom[u];
						prevLevel= level[w];
						int prevLevelW= level[w];
						level[w]= level[idom[u]]+1;

						updateDominatorTreeLevels(w);
						checkIncomingEdges(w);
						updateIds(w, idom[w], mode, prevLevelW);
						criticalPathCounter= 0;
					}else{
						noNewParentFlag= true;
					}

					return;
				}else{
					tmpArcPosition= r_Next[tmpArcPosition];
					while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= r_Next[tmpArcPosition];
					tmpArc= r_Target[tmpArcPosition];
				}
			}

			criticalPathCounter++;
			u= criticalPath[criticalPathCounter];
		}else{
			idom[w]= c;
			prevLevel= level[w];
			int prevLevelW= level[w];
			level[w]= level[c]+1;

			updateDominatorTreeLevels(w);

			int tmpDerivedArcPosition= derivedOutFirst[c];
			while(tmpArcPosition != 0 && Target[tmpArcPosition] != w) tmpDerivedArcPosition= derivedOutNext[tmpDerivedArcPosition];

			if(tmpDerivedArcPosition != 0) derivedArcFromDominator[w]= true;
			if(tmpArcPosition != 0 && (!(derivedInTarget[tmpDerivedArcPosition] == c && derivedOutTarget[tmpDerivedArcPosition] == w))){
				if(removeFromDerivedGraph(tmpDerivedArcPosition, false)){
					derivedGraphInSiblings[w]--;
				}

				fixGrArcAfterDeletion(tmpArcPosition);

				correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(c, w);
				fixGrArcAfterInsertion(tmpArcPosition);
			}

			checkIncomingEdges(w);
			updateIds(w, idom[w], mode, prevLevelW);

			return;
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
void processQList(int y, int c, int lowHighDominator, int mode){
	int w= 0;

	QListCounter= 0;
	if(c == -1){
		while(QListCounter != nodesInQList){
			w= QList[QListCounter];
			locateNewParent(w, c, y, mode);
			if(noNewParentFlag == false) updateInSiblings(w, c, lowHighDominator, mode);

			QListCounter++;
		}
	}else{
		while(QListCounter != nodesInQList){
			w= QList[QListCounter];

			locateNewParent(w, c, y, mode);
			if(noNewParentFlag == false) updateInSiblings(w, c, lowHighDominator, mode);

			QListCounter++;
		}
	}
}

inline void sortTriples(){
	int nodes= n+1;
	int* Triples2 = new int[3*triplesCounter];
	int* Count = new int[nodes+2];

	for(int i=2; i >= 0; i--){		//do this for every number of the triple
		for(int j=0; j <=nodes; j++) Count[j] = 0; //initialize
		for(int j=0; j < triplesCounter; j++) Count[triples[3*j+i]+1]++;  //count how many times every value apears
		for(int j=1; j <=nodes; j++) Count[j]+= Count[j-1];
		for(int j=0; j < triplesCounter; j++){ //insert triples into array in right order
			int k = Count[triples[3*j+i]];

			Triples2[3*k]   = triples[3*j];
			Triples2[3*k+1] = triples[3*j+1];
			Triples2[3*k+2] = triples[3*j+2];
			Count[triples[3*j+i]]++;
		}

		for (int j=0; j < 3*triplesCounter; j++) triples[j]= Triples2[j]; //copy the triples to the original array
	}

	delete [] Triples2;
	delete [] Count;
}

void processTriples(){
	int x= 0, y= 0;
	int prevX= 0, prevY= 0;
	int tmpArcPosition= 0;
	int dArcPosition= 0;

	for(int i= 0; i < triplesCounter; i++){
		if(triples[3*i+2] == 0){
			x= label2preorderDominator[triples[3*i+1]];
		}else{
			int source= label2preorderDominator[triples[3*i+1]];
			y= label2preorderDominator[triples[3*i+2]];
			tmpArcPosition= findGraphsArcPosition(source, y);

			if((prevX != x || prevY != y) && x != y){
				if(x != 0){
					correspondingDerivedArc[tmpArcPosition]= addToDerivedGraph(x, y);
					fixGrArcAfterInsertion(tmpArcPosition);
				}

				prevX= x;
				prevY= y;
			}else{ // derived arc (x,y) already in derived graph
				int tmpPosition= derivedOutFirst[x];
				int tmpNode= derivedOutTarget[tmpPosition];

				if(x != y){
					while(tmpPosition != 0){
						if(tmpNode == y){
							correspondingDerivedArc[tmpArcPosition]= tmpPosition;
							derivedArcCounter[tmpPosition]++;

							int grArcPosition= correspondingGraphArc[correspondingDerivedArc[tmpArcPosition]];
							correspondingGraphArc[correspondingDerivedArc[tmpArcPosition]]= tmpArcPosition;
							nextArcWithTheSameDerivedArc[tmpArcPosition]= grArcPosition;
							prevArcWithTheSameDerivedArc[grArcPosition]= tmpArcPosition;

							break;
						}else{
							tmpPosition= derivedOutNext[tmpPosition];
							tmpNode= derivedOutTarget[tmpPosition];
						}
					}
				}
			}
		}
	}
}

void addTriple(int x, int y, int z){
	if(y != 0){
		triples[3*triplesCounter]= x;
		triples[3*triplesCounter+1]= y;
		triples[3*triplesCounter+2]= z;

		triplesCounter++;
	}
}

void resetQList(){
	for(int i= nodesInQList-1; i>=0; i--) inQList[QList[i]]= 0;
	for(int i= nodesInQList-1; i>=0; i--) QList[i]= 0;
	
	nodesInQList= 0;
}

void scanNode(int node){
	int tmpPosition= derivedOutLowHighFirst[node];
	int tmpNode= derivedOutLowHighTarget[tmpPosition];
	int tmpDerivedArc1= 0;
	int tmpDerivedArc2= 0;
	int nextPosition= 0;
	int lowHighFlag= 0;
	bool nextPositionFlag= false;

	while(tmpPosition != 0){
		nextPosition= derivedOutLowHighNext[tmpPosition];

		if(derivedArcFromDominator[tmpNode] == false && inViolatingLowHigh[tmpNode] == false){
			if(derivedInLowHigh[tmpNode][0] == node || derivedInLowHigh[tmpNode][1] == node){
				(lowHighId[node] < lowHighId[tmpNode]) ? lowHighFlag= 0 : lowHighFlag= 1;

				int tmpDerivedPosition= derivedInFirst[tmpNode];
				int tmpDerivedNode= derivedInTarget[tmpDerivedPosition];

				if(lowHighFlag == 0){ // find one of the derived arcs with lower id
					while(tmpDerivedPosition != 0){
						if(lowHighId[tmpDerivedNode] < lowHighId[tmpNode] && inViolatingLowHigh[tmpDerivedNode] == false){
							break;
						}else{
							tmpDerivedPosition= derivedInNext[tmpDerivedPosition];
							tmpDerivedNode= derivedInTarget[tmpDerivedPosition];
						}
					}
				}else{ // find one of the derived arcs with higher id
					while(tmpDerivedPosition != 0){
						if(lowHighId[tmpDerivedNode] > lowHighId[tmpNode] && inViolatingLowHigh[tmpDerivedNode] == false){
								break;
						}else{
							tmpDerivedPosition= derivedInNext[tmpDerivedPosition];
							tmpDerivedNode= derivedInTarget[tmpDerivedPosition];
						}
					}
				}

				if(tmpDerivedNode == 0){
					addToViolatingLowHigh(tmpNode);
				}else{
					int tmpDerivedArcPosition= removeFromDerivedOutLowHigh(tmpNode, node);
					if(nextPosition == derivedOutLowHighCurrentPosition) nextPosition= tmpDerivedArcPosition; // derived arc changed position
						
					addToDerivedOutLowHigh(tmpNode, tmpDerivedNode);
					if(derivedInLowHigh[tmpNode][0] == 0){
						derivedInLowHigh[tmpNode][0]= tmpDerivedNode;
						derivedInLowHighReversePosition[tmpNode][0]= derivedOutLowHighCurrentPosition-1;
						derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
					}else{
						derivedInLowHigh[tmpNode][1]= tmpDerivedNode;
						derivedInLowHighReversePosition[tmpNode][1]= derivedOutLowHighCurrentPosition-1;
						derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= tmpNode;
					}
				}
			}
		}

		tmpPosition= nextPosition;
		tmpNode= derivedOutLowHighTarget[tmpPosition];
	}
}

void dfsNeedUpdateLowHigh(int node){
	int tmpNode, tmpPosition;

	visited[node]= true;
	visitedNodes[visitedNodesCounter]= node;
	visitedNodesCounter++;

	tmpPosition= derivedOutFirst[node];
	tmpNode= derivedOutTarget[tmpPosition];
	while(tmpNode != 0){
		if(visited[tmpNode] == false && inNeedUpdateLowHigh[node] == true) dfsNeedUpdateLowHigh(tmpNode);

		tmpPosition= derivedOutNext[tmpPosition];
		tmpNode= derivedOutTarget[tmpPosition];
	}

	if(inNeedUpdateLowHigh[node] == true && inNeedUpdateLowHighSorted[node] == false){
		needUpdateLowHighSorted[topologicalOrderCounter]= node;
		inNeedUpdateLowHighSorted[node]= true;
		topologicalOrderCounter--;
	}
}

void processNeedUpdateLowHigh(){
	int currentNode= 0;
	bool removeChildFromLowHighFlag= false;

	topologicalOrderCounter= needUpdateLowHighCounter-1;
	for(int i= 0; i < needUpdateLowHighCounter; i++){
		if(visited[needUpdateLowHigh[i]] == false) dfsNeedUpdateLowHigh(needUpdateLowHigh[i]);
	}

	for(int i= 0; needUpdateLowHighSorted[i] != 0; i++) needUpdateLowHigh[i]= needUpdateLowHighSorted[i]; // copy sorted table

	for(int i= 0; needUpdateLowHigh[i] != 0; i++){
		currentNode= needUpdateLowHigh[i];

		removeChildFromLowHighFlag= removeChildFromLowHigh(currentNode, prevIdom[currentNode]);
		if(removeChildFromLowHighFlag == true) addChildToLowHigh(currentNode, idom[currentNode]);
		inLowHighOrder[currentNode]= true;
		inNeedUpdateLowHigh[currentNode]= false;

		prevIdom[currentNode]= idom[currentNode];
	}
}

void updateLowHigh(){
	int tmpCounter= 0;

	while(violatingLowHigh[tmpCounter] != 0){
		scanNode(violatingLowHigh[tmpCounter]);
		addToNeedUpdateLowHigh(violatingLowHigh[tmpCounter]);
		
		tmpCounter++;
	}

	processNeedUpdateLowHigh();
}

void resetLowHighAuxiliariesLists(){
	for(int i= violatingLowHighCounter-1; i>=0; i--) inViolatingLowHigh[violatingLowHigh[i]]= false;
	for(int i= violatingLowHighCounter-1; i>=0; i--) positionInViolatingLowHigh[violatingLowHigh[i]]= 0;
	for(int i= violatingLowHighCounter-1; i>=0; i--) violatingLowHigh[i]= 0;
	
	for(int i= needUpdateLowHighCounter-1; i>=0; i--) inNeedUpdateLowHigh[needUpdateLowHigh[i]]= false;
	for(int i= needUpdateLowHighCounter-1; i>=0; i--) needUpdateLowHigh[i]= 0;
	for(int i= needUpdateLowHighCounter-1; i>=0; i--) inNeedUpdateLowHighSorted[needUpdateLowHighSorted[i]]= false;
	for(int i= needUpdateLowHighCounter-1; i>=0; i--) needUpdateLowHighSorted[i]= 0;
	
	for(int i= visitedNodesCounter-1; i>=0; i--) visited[visitedNodes[i]]= false;
	for(int i= visitedNodesCounter-1; i>=0; i--) visitedNodes[i]= 0;
	
	violatingLowHighCounter= 0;
	needUpdateLowHighCounter= 0;
	needUpdateLowHighSortedCounter= 0;
	visitedNodesCounter= 0;
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
inline void deleteReachable(int removedArcsPosition, int mode){
	int x= r_Target[removedArcsPosition];
	int y= Target[removedArcsPosition];
	int f= x; // the child of d(y) that's an ancestor of x
	int c= 0;
	int levelIdomY= level[idom[y]];
	int tmpLevel= level[x];
	int tmpNode= 0;
	int tmpPosition= 0;
	int value= -1;
	bool flag= true;

	resetQList();
	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) resetLowHighAuxiliariesLists();
	criticalPathFlag= false;
	prevLevel= level[x];
	value= removeFromDerivedGraph(correspondingDerivedArc[removedArcsPosition], true);
	fixGrArcAfterDeletion(removedArcsPosition);

	if(idom[y] != x){
		while(levelIdomY != tmpLevel &&  levelIdomY+1 < tmpLevel){
			f= idom[f];
			tmpLevel= level[f];
		}

		tmpPosition= r_First[y];
		while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
		tmpNode= r_Target[tmpPosition];
		while(flag == true && tmpNode != 0){
			if(isChild(f, tmpNode)){ // tmpNode descendant of f
				flag= false;
			}else{
				tmpPosition= r_Next[tmpPosition];
				while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
				tmpNode= r_Target[tmpPosition];
			}
		}

		if(flag == true && value != 0){
			derivedGraphInSiblings[y]--;
		}
	}

	if(derivedGraphInSiblings[y] >= 2){
		if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
		if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();

		return;
	}else{
		flag= false;

		tmpPosition= r_First[y];
		while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];

		if(r_Target[tmpPosition] == idom[y]){
			flag= true;
		}else{
			while(r_Target[tmpPosition] != 0 && r_Target[tmpPosition] != idom[y]){
				tmpPosition= r_Next[tmpPosition];
				while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];

				if(r_Target[tmpPosition] == idom[y]) flag= true;
			}
		}

		if(flag == true){
			if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
			if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();

			return;
		}
	}

	// compute the nca of In(y)
	int z= 0;
	int tmp1= 0;
	int tmp2= 0;
	tmpPosition= r_First[y];
	while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
	tmpNode= r_Target[tmpPosition];

	while(level[tmpNode] == 0){ // incoming arc from unreachable node
		tmpPosition= r_Next[tmpPosition];
		tmpNode= r_Target[tmpPosition];
	}

	tmp1= tmpNode;
	tmpPosition= r_Next[tmpPosition];
	while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
	tmpNode= r_Target[tmpPosition];

	while(tmpNode != 0 && level[tmpNode] == 0){ // incoming arc from unreachable node
		tmpPosition= r_Next[tmpPosition];
		tmpNode= r_Target[tmpPosition];
	}

	tmp2= tmpNode;
	while(tmp2 != 0 && tmp1 != tmp2){
		(level[tmp1] < level[tmp2]) ? tmp2= idom[tmp2] : tmp1= idom[tmp1];
	}

	z= tmp1;
	tmpPosition= r_Next[tmpPosition];
	while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
	tmp2= r_Target[tmpPosition];

	while(tmp2 != 0){
		while(level[tmp2] != 0 && tmp1 != tmp2){
			(level[tmp1] < level[tmp2]) ? tmp2= idom[tmp2] : tmp1= idom[tmp1];
		}
		z= tmp1;

		tmpPosition= r_Next[tmpPosition];
		while(tmpPosition != 0 && validArc[tmpPosition] == false) tmpPosition= r_Next[tmpPosition];
		tmp2= r_Target[tmpPosition];
	}

	if(z == idom[y]){
		if(mode == 0 && violatingLowHighFlag == true) addToViolatingLowHigh(y);
		if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();

		return;
	}

	c= z;
	while(levelIdomY+1 != level[c]){
		c= idom[c];
	}

	idom[y]= z;
	prevLevel= level[y];
	int prevLevelY= level[y];
	level[y]= level[z]+1;

	checkIncomingEdges(y);
	updateIds(y, idom[y], mode, prevLevelY);
	
	int lowHighDominatorNode= prevIdom[y]; 
	updateInSiblings(y, c, prevIdom[y], mode);
	updateDominatorTreeLevels(y);
	processQList(y, c, lowHighDominatorNode, mode);

	if(derivedArcFromDominator[y] == false) fixDerivedArcFromDominator(y);
	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == true) updateLowHigh();
	prevIdom[y]= idom[y];
}

void constructDerivedfGraph(){
	int nodes= n+1;
	int y= 0;
	int arcsPosition= 0;

	for(int i= 1; i <= nodes; i++){
		if(idom[i] != 0){
			addTriple(preorder2labelDominator[idom[i]], preorder2labelDominator[i], 0);
		}
	}

	for(int x= 1; x <= nodes; x++){
		for(int j= First[x]; j != 0; j= Next[j]){
			y= Target[j];

			if(idom[x] != 0 && idom[y] != 0){
				// (algorithm 3 (page 13 Dominator Tree Certification anmd Divergent Spanning Trees))
				if(preorder2labelDominator[y] <= preorder2labelDominator[x] && preorder2labelDominator[x] < preorder2labelDominator[y]+size[y]){ // step 2
					continue; // acyclic
				}else if(x == idom[y]){ // step 3 (x,y) -> derived arc
					arcsPosition= findGraphsArcPosition(x, y);
					correspondingDerivedArc[arcsPosition]= addToDerivedGraph(x, y);
					fixGrArcAfterInsertion(arcsPosition);
				}else{ // step 4
					addTriple(preorder2labelDominator[idom[y]], preorder2labelDominator[x], preorder2labelDominator[y]);
				}
			}else{
				validArc[j]= false;
			}
		}
	}

	sortTriples(); // step 5
	processTriples(); // step 6
}

void constructLowHigh(){
	int topologicalNode= 0;
	int derivedArcLeft= 0;
	int derivedArcRight= 0;
	int dominator= 0;
	int tmpPosition= 0;
	int tmpNode= 0;
	int siblingsWithDerivedArcFromDominator= 0;
	int left= 0;
	int right= 0;
	bool derivedArcFromIdom= false;
	
	for(int i= topologicalOrderCounter+1; i < n; i++){
		if(idom[topologicalOrder[i]] != 0){
			derivedArcLeft= 0;
			derivedArcRight= 0;
			siblingsInLowHighOrderCounter= 0;
			left= 0;
			right= 0;

			topologicalNode= topologicalOrder[i];
			inLowHighOrder[topologicalNode]= true;
			derivedArcFromIdom= derivedArcFromDominator[topologicalNode];

			if(topologicalNode != r){
				tmpPosition= derivedInFirst[topologicalNode];
				tmpNode= derivedInTarget[tmpPosition];

				while(tmpPosition != 0){
					if(tmpNode == idom[topologicalNode]){
						derivedArcFromIdom= true;
					}else if(inLowHighOrder[tmpNode] == true){
						siblingsInLowHighOrder[siblingsInLowHighOrderCounter]= tmpNode;
						siblingsInLowHighOrderCounter++;
					}

					tmpPosition= derivedInNext[tmpPosition];
					tmpNode= derivedInTarget[tmpPosition];
				}

				siblingsInLowHighOrder[siblingsInLowHighOrderCounter]= 0;
				dominator= idom[topologicalNode];

				if(derivedArcFromIdom == true){
					if(lowHighHead[dominator] == 0){
						lowHighHead[dominator]= topologicalNode;
						giveNodeLowHighId(topologicalNode, 0, 0);
					}else if(siblingsInLowHighOrderCounter == 0){
						lowHighPrevNode[lowHighHead[dominator]]= topologicalNode;
						lowHighNextNode[topologicalNode]= lowHighHead[dominator];
						lowHighHead[dominator]= topologicalNode;
						giveNodeLowHighId(topologicalNode, 0, lowHighNextNode[topologicalNode]);
					}else if(siblingsInLowHighOrderCounter == 1){ // only two derived arcs (one of them from dominator)
						lowHighPrevNode[lowHighHead[dominator]]= topologicalNode;
						lowHighNextNode[topologicalNode]= lowHighHead[dominator];
						lowHighHead[dominator]= topologicalNode;
						giveNodeLowHighId(topologicalNode, 0, lowHighNextNode[topologicalNode]);
					}else{ // at least 2 derived arcs
						quickSortSiblingsInLowHighOrder(0, siblingsInLowHighOrderCounter-1);

						left= (siblingsInLowHighOrderCounter-1)/2;
						right= left+1;
						derivedArcLeft= siblingsInLowHighOrder[left];
						derivedArcRight= lowHighNextNode[derivedArcLeft];
					
						lowHighNextNode[derivedArcLeft]= topologicalNode;
						lowHighPrevNode[topologicalNode]= derivedArcLeft;
						lowHighPrevNode[derivedArcRight]= topologicalNode;
						lowHighNextNode[topologicalNode]= derivedArcRight;
						giveNodeLowHighId(topologicalNode, lowHighPrevNode[topologicalNode], lowHighNextNode[topologicalNode]);
					}

					derivedInLowHigh[topologicalNode][0]= idom[topologicalNode];
					derivedInLowHigh[topologicalNode][1]= idom[topologicalNode];
				}else{ // at least 2 derived arcs
					quickSortSiblingsInLowHighOrder(0, siblingsInLowHighOrderCounter-1);

					left= (siblingsInLowHighOrderCounter-1)/2;
					right= left+1;
					derivedArcLeft= siblingsInLowHighOrder[left];
					derivedArcRight= lowHighNextNode[derivedArcLeft];

					lowHighNextNode[derivedArcLeft]= topologicalNode;
					lowHighPrevNode[topologicalNode]= derivedArcLeft;
					lowHighPrevNode[derivedArcRight]= topologicalNode;
					lowHighNextNode[topologicalNode]= derivedArcRight;
					giveNodeLowHighId(topologicalNode, lowHighPrevNode[topologicalNode], lowHighNextNode[topologicalNode]);
				
					addToDerivedOutLowHigh(topologicalNode, siblingsInLowHighOrder[left]);
					derivedInLowHigh[topologicalNode][0]= siblingsInLowHighOrder[left];
					derivedInLowHighReversePosition[topologicalNode][0]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= topologicalNode;

					addToDerivedOutLowHigh(topologicalNode, siblingsInLowHighOrder[right]);
					derivedInLowHigh[topologicalNode][1]= siblingsInLowHighOrder[right];
					derivedInLowHighReversePosition[topologicalNode][1]= derivedOutLowHighCurrentPosition-1;
					derivedInLowHighReverseNode[derivedOutLowHighCurrentPosition-1]= topologicalNode;
				}

				inLowHighChildrenList[topologicalNode]= true;
			}
		}
	}
}

// mode == 0 -> updates low high
// mode == 1 -> without updating of low high
inline void deleteUnreachable(int arcsPosition, int mode){
	int x= r_Target[arcsPosition];
	int y= Target[arcsPosition];
	int source= y;

	resetQList();
	if(mode == 0) resetLowHighAuxiliariesLists();

	while(isChild(y, source)){
		int position= First[source];
		while(position != 0 && validArc[position] == false) position= Next[position];
		int target= Target[position];
		int nextPosition= 0;

		while(position != 0){
			if(!isChild(y, target)){
				nextPosition= Next[position];
				while(nextPosition != 0 && validArc[nextPosition] == false) nextPosition= Next[nextPosition];
				int newlyremovedArcPosition= delete_arc_from_graph(source, target, 1);

				if(idom[source] != 0){
					nca = intersectLevel(source, target);
					if(target != nca && x != source && y != target){
						deleteReachable(newlyremovedArcPosition, mode);
						resetQList();
					}
				}

				position= nextPosition;
			}else{
				prevLevel= level[target];
				removeFromDerivedGraph(correspondingDerivedArc[position], false);
				fixGrArcAfterDeletion(position);
				position= Next[position];
				while(position != 0 && validArc[position] == false) position= Next[position];
			}

			target= Target[position];
		}

		if(nodesTablePostorder[source]->leftNode != NULL){
			source= nodesTablePostorder[source]->leftNode->nodesName;
		}else if(nodesTablePostorder[source]->rep->leftRepresentative != NULL){
			source= nodesTablePostorder[source]->rep->leftRepresentative->nodesListTail->nodesName;
		}else{
			break;
		}
	}

	prevLevel= level[y];
	removeFromDerivedGraph(correspondingDerivedArc[arcsPosition], false);
	fixGrArcAfterDeletion(arcsPosition);
	updateIds(y, -1, mode, -1);

	if(mode == 0 && executeProcessNeedUpdateLowHighFlag == false){
		updateLowHigh();
	}

	if(mode == 0) removeChildFromLowHigh(y, prevIdom[y]);
	
	idom[y]= 0;
	prevIdom[y]= 0;
	level[y]= 0;
}

void createLowHighVerifierFile(char *filename){
	char *tmpPosition= strstr(filename, "output.txt");

	if(tmpPosition != NULL){
		strcpy(tmpPosition, "output_lowHigh.txt");
	}else{
		strcpy(filename, "outputLowHigh.txt");
	}

	FILE *output;
	output= fopen(filename, "w+");

	int edges= 0;
	int tmpPos= 0;
	int tmpNode= 0;

	for(int i= 1; i < n+1; i++){
		tmpPos= First[i];
		tmpNode= Target[tmpPos];

		while(tmpPos != 0){
			if(validArc[tmpPos] == true) edges++;
			tmpPos= Next[tmpPos];
			while(tmpPos != 0 && validArc[tmpPos] == false) tmpPos= Next[tmpPos];
			tmpNode= Target[tmpPos];
		}
	}

	fprintf(output, "p %d %d %d %d\n", n, edges, r, r);

	for(int i= 1; i < n+1; i++){
		tmpPos= First[i];
		while(tmpPos != 0 && validArc[tmpPos] == false) tmpPos= Next[tmpPos];
		tmpNode= Target[tmpPos];

		while(tmpPos != 0){
			if(validArc[tmpPos] == true) fprintf(output, "a %d %d\n", i, tmpNode);
			tmpPos= Next[tmpPos];
			while(tmpPos != 0 && validArc[tmpPos] == false) tmpPos= Next[tmpPos];
			tmpNode= Target[tmpPos];
		}
	}

	fprintf(output, "d %d %d\n", r, r);
	for(int i= 1; i < n+1; i++){
		tmpNode= lowHighHead[i];

		while(tmpNode != 0){
			fprintf(output, "d %d %d\n", idom[tmpNode], tmpNode);
			tmpNode= lowHighNextNode[tmpNode];
		}
	}
}

void deleteArc(int arcsPosition) {
	int x= r_Target[arcsPosition];
	int y= Target[arcsPosition];
	int idomy = idom[y];

	if (!idom[x]) return;

	nca = intersectLevel(x, y);

	if (y == nca) return; // y dominates x - nothing else to do
	
	if(x == idomy){ // y may become unreachable
		// test if y is reachable from idomy
		if(isReachable(y)){
			executeProcessNeedUpdateLowHighFlag= true;
			deleteReachable(arcsPosition, UPDATE_LOW_HIGH);
		}else{
			executeProcessNeedUpdateLowHighFlag= false;
			deleteUnreachable(arcsPosition, UPDATE_LOW_HIGH);
		}
	}else{
		executeProcessNeedUpdateLowHighFlag= true;
		deleteReachable(arcsPosition, UPDATE_LOW_HIGH); // y reachable
	}
}

// search successors of v for affected vertices
void visit(int v){
	int selected_node= 0;
	int tmpArcPosition= 0;

	// process edges leaving v
	tmpArcPosition= First[v];
	while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= Next[tmpArcPosition];
	while(tmpArcPosition != 0){
		selected_node= Target[tmpArcPosition];

		if(!(level[selected_node] > level[nca]+1) || visited[selected_node]){
			tmpArcPosition= Next[tmpArcPosition];
			while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= Next[tmpArcPosition];
			continue;
		}

		// if selected_node is affected
		if(ancestor_of_y[idom[selected_node]] && level[idom[selected_node]] < rootLevel){
			affected[selected_node]= true;
			visited[selected_node]= true;

			if(ancestor_of_y[selected_node] && level[selected_node] < minDepth) minDepth= level[selected_node];
			if(!ancestor_of_y[selected_node]){
				affectedQueue[affectedQueueLast++]= selected_node;
				visit(selected_node);
			} 
		}else if(visited[idom[selected_node]]){// selected_node is scanned but not affected
			visited[selected_node]= true;
			levelQueue[levelQueueLast++]= selected_node;
			inLevelQueue[selected_node]= true;
			visit(selected_node);
		}

		tmpArcPosition= Next[tmpArcPosition];
		while(tmpArcPosition != 0 && validArc[tmpArcPosition] == false) tmpArcPosition= Next[tmpArcPosition];
	}
}

void updateDerivedGraphAfterInsertion(int node, int newDerivedSource){
	int tmpDerivedArcPosition= derivedOutFirst[node];
	int tmpDerivedArcNext= 0;
	int tmpGraphArcPosition= 0;
	int tmpGraphArcNext= 0;
	int source= 0;
	int target= 0;
	int tmpCounter= 0;

	while(tmpDerivedArcPosition != 0){
		tmpDerivedArcNext= derivedOutNext[tmpDerivedArcPosition];
		tmpGraphArcPosition= correspondingGraphArc[tmpDerivedArcPosition];

		tmpCounter= derivedArcCounter[tmpDerivedArcPosition];
		source= r_Target[tmpGraphArcPosition];
		target= Target[tmpGraphArcPosition];

		for(int i= 0; i< tmpCounter; i++){
			if(isChild(newDerivedSource, source)){
				if(!(derivedInTarget[tmpDerivedArcPosition] == newDerivedSource && derivedOutTarget[tmpDerivedArcPosition] == target)){
					removeFromDerivedGraph(tmpDerivedArcPosition, false);
					if(tmpGraphArcPosition != 0) tmpGraphArcNext= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];
					fixGrArcAfterDeletion(tmpGraphArcPosition);

					if(tmpDerivedArcNext == derivedGraphCurrentPosition) tmpDerivedArcNext= tmpDerivedArcPosition; // derived arc changed position

					correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(newDerivedSource, target);
					fixGrArcAfterInsertion(tmpGraphArcPosition);
					correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;

					tmpGraphArcPosition= tmpGraphArcNext;

					if(tmpGraphArcPosition != 0){
						source= r_Target[tmpGraphArcPosition];
						target= Target[tmpGraphArcPosition];
					}
				}
			}else{
				if(tmpGraphArcPosition != 0) tmpGraphArcPosition= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];

				if(tmpGraphArcPosition != 0){
					source= r_Target[tmpGraphArcPosition];
					target= Target[tmpGraphArcPosition];
				}
			}
		}

		tmpDerivedArcPosition= tmpDerivedArcNext;
	}
}

// update levels of visited (but not affected) vertices
void updateLevels(){
	int v= 0;
	int tmpGraphArcPosition= 0;
	int newDerivedSource= 0;
	int tmpCounter= levelQueueFirst;

	while(levelQueueFirst < levelQueueLast){
		v= levelQueue[levelQueueFirst++];
		level[v]= level[idom[v]]+1;
		visited[v]= false;
	}

	levelQueueFirst= tmpCounter;
	while(levelQueueFirst < levelQueueLast){
		v= levelQueue[levelQueueFirst++];
		tmpGraphArcPosition= First[v];
		while(tmpGraphArcPosition != 0 && validArc[tmpGraphArcPosition] == false) tmpGraphArcPosition= Next[tmpGraphArcPosition];

		while(tmpGraphArcPosition != 0){
			if(!(derivedInTarget[correspondingDerivedArc[tmpGraphArcPosition]] == newDerivedSource && derivedOutTarget[correspondingDerivedArc[tmpGraphArcPosition]] == Target[tmpGraphArcPosition])){
				if(derivedInTarget[correspondingDerivedArc[tmpGraphArcPosition]] != idom[derivedOutTarget[correspondingDerivedArc[tmpGraphArcPosition]]]) derivedGraphInSiblings[derivedOutTarget[correspondingDerivedArc[tmpGraphArcPosition]]]--;
				if(removeFromDerivedGraph(correspondingDerivedArc[tmpGraphArcPosition], false) == 0) derivedGraphInSiblings[derivedOutTarget[correspondingDerivedArc[tmpGraphArcPosition]]]++; // derived arc has multiple copies
				fixGrArcAfterDeletion(tmpGraphArcPosition);
			
				newDerivedSource= r_Target[tmpGraphArcPosition];
				while(level[newDerivedSource] > level[Target[tmpGraphArcPosition]]) newDerivedSource= idom[newDerivedSource];

				correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(newDerivedSource, Target[tmpGraphArcPosition]);
				fixGrArcAfterInsertion(tmpGraphArcPosition);
				correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;
			}
			
			tmpGraphArcPosition= Next[tmpGraphArcPosition];
		}
	}

	for(int i= tmpCounter; i<levelQueueLast; i++){
		inLevelQueue[levelQueue[i]]= false;
		levelQueue[i]= 0;
	}
}

void updateDerivedGraphForAffected(int affectedNode, int newDerivedSource, int y){
	int tmpDerivedArcPosition= 0;
	int tmpDerivedArcNext= 0;
	int tmpNode= 0;
	int tmpGraphArcPosition= 0;
	int tmpGraphArcNextPosition= 0;
	int source= 0;
	int target= 0;
	int tmpCounter= 0;
	nodesInAffectedNodeSubtreeCounter= 0;

	nodesInAffectedNodeSubtree[nodesInAffectedNodeSubtreeCounter]= affectedNode;
	inAffectedNodeSubtree[affectedNode]= true;
	nodesInAffectedNodeSubtreeCounter++;

	for(int i= 0; i< nodesInAffectedNodeSubtreeCounter; i++){
		tmpNode= nodesInAffectedNodeSubtree[i];
		tmpGraphArcPosition= First[tmpNode];

		while(tmpGraphArcPosition != 0){
			target= Target[tmpGraphArcPosition];

			if(inAffectedNodeSubtree[target] == false && isChild(tmpNode, target)){
				nodesInAffectedNodeSubtree[nodesInAffectedNodeSubtreeCounter]= target;
				inAffectedNodeSubtree[target]= true;
				nodesInAffectedNodeSubtreeCounter++;
			}

			tmpDerivedArcPosition= correspondingDerivedArc[tmpGraphArcPosition];

			if(derivedInTarget[tmpDerivedArcPosition] == newDerivedSource){
				if(derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]--;
				if(removeFromDerivedGraph(tmpDerivedArcPosition, false) == 0 && derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]++; // derived arc has multiple copies
				fixGrArcAfterDeletion(tmpGraphArcPosition);

				correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(affectedNode, target);
				fixGrArcAfterInsertion(tmpGraphArcPosition);
				correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;
			}

			tmpGraphArcPosition= Next[tmpGraphArcPosition];
		}
	}

	for(int i= 0; i< nodesInAffectedNodeSubtreeCounter; i++){
		inAffectedNodeSubtree[nodesInAffectedNodeSubtree[i]]= false;
		nodesInAffectedNodeSubtree[i]= 0;
	}			

	tmpDerivedArcPosition= derivedInFirst[affectedNode];
	while(tmpDerivedArcPosition != 0){
		tmpDerivedArcNext= derivedInNext[tmpDerivedArcPosition];
		tmpGraphArcPosition= correspondingGraphArc[tmpDerivedArcPosition];
		tmpCounter= derivedArcCounter[tmpDerivedArcPosition];

		for(int i= 0; i< tmpCounter; i++){
			source= r_Target[tmpGraphArcPosition];
			target= Target[tmpGraphArcPosition];
			
			if(level[target] > level[source] && inLevelQueue[source] == false){
				if(derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]--;
				if(removeFromDerivedGraph(tmpDerivedArcPosition, false) == 0 && derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]++; // derived arc has multiple copies
				if(tmpGraphArcPosition != 0) tmpGraphArcNextPosition= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];
				fixGrArcAfterDeletion(tmpGraphArcPosition);

				if(tmpDerivedArcNext == derivedGraphCurrentPosition) tmpDerivedArcNext= tmpDerivedArcPosition; // derived arc changed position

				newDerivedSource= target;
				while(level[newDerivedSource] > level[source]) newDerivedSource= idom[newDerivedSource];
				correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(newDerivedSource, target);
				fixGrArcAfterInsertion(tmpGraphArcPosition);
				correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;
			}else if(level[source] > level[target] && inLevelQueue[source] == false){
				if(derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]--;
				if(removeFromDerivedGraph(tmpDerivedArcPosition, false) == 0 && derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]++; // derived arc has multiple copies
				if(tmpGraphArcPosition != 0) tmpGraphArcNextPosition= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];
				fixGrArcAfterDeletion(tmpGraphArcPosition);

				if(tmpDerivedArcNext == derivedGraphCurrentPosition) tmpDerivedArcNext= tmpDerivedArcPosition; // derived arc changed position

				newDerivedSource= source;
				while(level[newDerivedSource] > level[target]) newDerivedSource= idom[newDerivedSource];
				correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(newDerivedSource, target);
				fixGrArcAfterInsertion(tmpGraphArcPosition);
				correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;
			}else if(level[source] == level[target] && inLevelQueue[source] == false){
				if(derivedInTarget[tmpDerivedArcPosition] == prevIdom[derivedOutTarget[tmpDerivedArcPosition]] && derivedArcCounter[tmpDerivedArcPosition] > 1){ // arc was from previous dominator (prevIdom) and now prevIdom is sibling with multiple edges
					derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]++;
				}else{
					if(derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]--;
					if(removeFromDerivedGraph(tmpDerivedArcPosition, false) == 0 && derivedInTarget[tmpDerivedArcPosition] != prevIdom[derivedOutTarget[tmpDerivedArcPosition]]) derivedGraphInSiblings[derivedOutTarget[tmpDerivedArcPosition]]++; // derived arc has multiple copies
					if(tmpGraphArcPosition != 0) tmpGraphArcNextPosition= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];
					fixGrArcAfterDeletion(tmpGraphArcPosition);

					if(tmpDerivedArcNext == derivedGraphCurrentPosition) tmpDerivedArcNext= tmpDerivedArcPosition; // derived arc changed position

					correspondingDerivedArc[tmpGraphArcPosition]= addToDerivedGraph(source, target);
					fixGrArcAfterInsertion(tmpGraphArcPosition);
					correspondingGraphArc[correspondingDerivedArc[tmpGraphArcPosition]]= tmpGraphArcPosition;
				}
			}else{
				tmpGraphArcNextPosition= nextArcWithTheSameDerivedArc[tmpGraphArcPosition];
			}

			tmpGraphArcPosition= tmpGraphArcNextPosition;
		}	

		tmpDerivedArcPosition= tmpDerivedArcNext;
	}
}

// update idom and level arrays
inline void updateDomtree(int y){
	int v= 0;
	int temp= 0;

	while(affectedQueueFirst < affectedQueueLast){
		v= affectedQueue[affectedQueueFirst++];

		temp= v;
		while(level[temp] != level[nca]+1) temp= idom[temp];

		int prevIdomV= idom[v];
		int prevLevelV= level[v];
		prevIdom[v]= idom[v];
		idom[v]= nca;
		derivedArcFromDominator[v]= false;

		updateIds(v, idom[v], 0, prevLevelV);

		level[v]= level[nca]+1; // update level
		affected[v]= visited[v]= false;
		dfsparent[v]= 0;

		updateDerivedGraphForAffected(v, temp, y);
		prevIdom[v]= idom[v];
	}

	updateLevels();
}

// inserted arc (x, y) is such that both x and y reachable before insertion
inline void insertReachable(int x, int y) {
	int search_vertex = y;
	int temp= y;

	nca= intersectLevel(x, y);
	if((nca == idom[y]) || (nca == y)) return;

	// mark the vertices on the path from nca to y in D
	do{
		ancestor_of_y[temp]= true;
		temp= idom[temp];
	}while(temp != nca);

	minDepth= level[y];
	affected[y]= true;
	bucketLevel= level[y];

	while(level[search_vertex] >= minDepth){
		rootLevel= level[search_vertex];
		visited[search_vertex]= true;
		affectedQueue[affectedQueueLast++]= search_vertex;

		visit(search_vertex);

		search_vertex= idom[search_vertex];
		while(level[search_vertex] > minDepth && !affected[search_vertex]){
			search_vertex= idom[search_vertex];
		}
	}

	temp= y;
	do{
		ancestor_of_y[temp]= false;
		temp= idom[temp];
	}while(temp != nca);

	updateDomtree(y);
}

// g was previously unreachable, now is at level l
void unreachable(int g){
	int u= 0, v= 0;
	int derivedU= 0;
	arcQueueFirst=0;
	arcQueueLast=0;

	snca(g, -1, 1);

	while(arcQueueFirst < arcQueueLast){
		u= arcQueue[arcQueueFirst++];
		v= arcQueue[arcQueueFirst++];

		int position= findGraphsArcPosition(u, v);
		validArc[position]= true;
		insertReachable(u, v);
		checkIncomingEdges(v);
	}
}

void insertArc(int position){
	int derivedX= 0;
	int sourceNode= r_Target[position];
	int targetNode= Target[position];

	if(!idom[sourceNode]) return; 
	if(idom[targetNode]){
		insertReachable(sourceNode, targetNode); // both x and y reachable

		derivedX= sourceNode;
		while(level[derivedX] != 1 && level[derivedX] > level[targetNode]) derivedX= idom[derivedX];
		correspondingDerivedArc[position]= addToDerivedGraph(derivedX, targetNode);
		fixGrArcAfterInsertion(position);
		correspondingGraphArc[correspondingDerivedArc[position]]= position;
		checkIncomingEdges(targetNode);
	}else{ // y was unreachable
		idom[targetNode]= sourceNode;
		level[targetNode]= level[sourceNode]+1;

		correspondingDerivedArc[position]= addToDerivedGraph(sourceNode, targetNode);
		fixGrArcAfterInsertion(position);
		correspondingGraphArc[correspondingDerivedArc[position]]= position;
		addToPreorderPostorderLists(targetNode, idom[targetNode]);
		unreachable(targetNode);
	}

	validArc[position]= true;
}

/* read graph from input file */
void readGraph(const char *file) {
	FILE *input = fopen(file, "r");
	if (!input) {
		fprintf(stderr, "Error opening file \"%s\".\n", file);
		exit(-1);
	}

	int x, y, dummy;
	int current_input_pos= 0;

	while (fgets(line, MAXLINE, input) != NULL) {
		switch (line[0]) {
		case '\n':;
		case '\0': break;
		case 'p':
			if(sscanf(line, "p %d %d %d %d", &n, &m, &r, &dummy) != 4){
				fprintf(stderr, "Error reading graph size (%s).\n", file);
				exit(-1);
			}

			input_file = new int[3*(m+1)];
			break;
		case 'a':
			if (sscanf(line, "a %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph arc (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_a;

			break;
		case 'e': //fprintf(stderr, "read e\n");
			input_file[current_input_pos++]= 0;
			input_file[current_input_pos++]= 0;
			input_file[current_input_pos++]= INPUT_e;

			break;
		case 'i':
			if (sscanf(line, "i %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph insertion (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_i;

			break;
		case 'd':
			if (sscanf(line, "d %d %d", &x, &y) != 2) {
				fprintf(stderr, "Error reading graph deletion (%s).\n", file);
				exit(-1);
			}

			input_file[current_input_pos++]= x;
			input_file[current_input_pos++]= y;
			input_file[current_input_pos++]= INPUT_d;

			break;
		default:
			fprintf(stderr, "Error reading graph (%s).\n", file);
			exit(-1);
		}
	}

	fclose(input);
}

// process input arcs
void processInput(){
	int input_source, input_target, input_type;
	int current_input_pos;

	for (current_input_pos = 0; current_input_pos <= 3 * m; current_input_pos += 3) {
		input_source = input_file[current_input_pos];
		input_target = input_file[current_input_pos + 1];
		input_type = input_file[current_input_pos + 2];
		switch (input_type) {
		case INPUT_a:
			insert_arc_to_graph(input_source, input_target);
			break;
		case INPUT_e:
			arcQueueFirst= arcQueueLast= affectedQueueFirst= affectedQueueLast= levelQueueFirst= levelQueueLast= 0;
			snca(r, -1, 0);
			initializeDominatorTreeStructures();
			constructDerivedfGraph();
			if(UPDATE_LOW_HIGH == 0) constructLowHigh();

			for(int i= n; i >= 0; i--) prevIdom[i]= idom[i];
			for(int i= visitedNodesCounter; i >= 0; i--) visitedNodes[i]= 0;
			visitedNodesCounter= 0;

			constructionPhase= false;
			break;
		case INPUT_i:
			insertionDeletionFlag= 1;
			if(idom[input_source] != 0){
				derivedArcFromDominator[input_target]= false;
				arcQueueFirst= arcQueueLast= affectedQueueFirst= affectedQueueLast= levelQueueFirst= levelQueueLast= 0;
				insertArc(insert_arc_to_graph(input_source, input_target));

				if(input_source == idom[input_target]) derivedArcFromDominator[input_target]= true;
			}else{ 
				insertArc(insert_arc_to_graph(input_source, input_target));
			}

			if(skippedFromDFSUCounter != 0){
				int derivedX, derivedY;

				for(int i= skippedFromDFSUCounter-1; i >= 0; i--){
					derivedX= r_Target[skippedFromDFSU[i]];
					derivedY= Target[skippedFromDFSU[i]];

					if(r_Target[skippedFromDFSU[i]] == idom[Target[skippedFromDFSU[i]]]){
						correspondingDerivedArc[skippedFromDFSU[i]]= addToDerivedGraph(derivedX, derivedY);
						fixGrArcAfterInsertion(skippedFromDFSU[i]);
						derivedArcFromDominator[derivedY]= true;
					}else{
						while(level[derivedX] > level[derivedY]){
							derivedX= idom[derivedX];
						}

						correspondingDerivedArc[skippedFromDFSU[i]]= addToDerivedGraph(derivedX, derivedY);
						fixGrArcAfterInsertion(skippedFromDFSU[i]);
					}					
					
					skippedFromDFSU[i]= 0;
				}

				skippedFromDFSUCounter= 0;
			}

			break;
		case INPUT_d:
			insertionDeletionFlag= 0;
			if(idom[input_source] != 0){
				int arcsPosition= delete_arc_from_graph(input_source, input_target, 0);
				deleteArc(arcsPosition);
				correspondingDerivedArc[arcsPosition]= 0;
			}

			break;
		default:
			fprintf(stderr, "Error reading graph.\n");
			exit(-1);
		}
	}
}

int main(int argc, char *argv[]) {
	if (argc != 2) {
		printf("\n usage: %s < input file>\n\n", argv[0]);
		exit(-1);
	}

	strcpy(file, argv[1]);
	readGraph(file);

	#ifdef _WIN32
		std::chrono::duration<double> totalTime;
		auto start = std::chrono::high_resolution_clock::now();
	#elif _linux
		RFWTimer timer(true);
		double t;
	#endif
	
	init(n + 1, m + 1);
	processInput();

	#ifdef _WIN32
		auto finish = std::chrono::high_resolution_clock::now();
		totalTime+= finish-start;
		printf("Total time= %g\n", totalTime);
	#elif _linux
		t = timer.getTime();
		printf("Total time= %g\n", t);
	#endif

	if(UPDATE_LOW_HIGH == 0) createLowHighVerifierFile(file);
}