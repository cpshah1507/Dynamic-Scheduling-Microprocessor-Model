#define __STDC_FORMAT_MACROS
#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>
#include <math.h>

#define REGSIZE 2048
#define ROBSIZE 1024

int scoreBoard[REGSIZE];
char tableCounter[65536];

struct node
{
    int data ;
    struct node *link ;
};

struct dqueue
{
    struct node *front ;
    struct node *rear ;
};


void initdqueue ( struct dqueue * ) ;
void addqatend ( struct dqueue *, int item ) ;
int delqatbeg ( struct dqueue * ) ;
void display ( struct dqueue ) ;
int count ( struct dqueue ) ;
void deldqueue ( struct dqueue * ) ;



/* initializes elements of structure */
void initdqueue ( struct dqueue *p )
{
    p ->  front = p -> rear = NULL ;
}

/* adds item at the end of dqueue */
void addqatend ( struct dqueue *p, int item )
{
    struct node *temp ;

    temp = ( struct node * ) malloc ( sizeof ( struct node )  );
    temp -> data = item ;
    temp -> link = NULL ;

    if ( p -> front == NULL )
        p -> front = temp ;
    else
        p -> rear -> link = temp ;
    p -> rear = temp ;
}

/* deletes item from begining of dqueue */
int delqatbeg ( struct dqueue *p )
{
    struct node *temp = p -> front ;
    int item ;
    if ( temp == NULL )
    {
        printf ( "\nQueue is empty." ) ;
        return 0 ;
    }
    else
    {
        temp = p -> front ;
        item = temp -> data ;
        p -> front = temp -> link ;
        free ( temp ) ;

        if ( temp == NULL )
            p -> rear = NULL ;
        return ( item ) ;
    }
}


struct opData
{
	int64_t microOpCount;
	int sourceRegs[3];
	int regReady[3];
	int destinationRegs[2];
	int isLoad;
	int isStore;
	uint64_t address;
	int64_t sequenceNum;
	int isIssued;
	int fetchCycle;
	int issueCycle;
	int doneCycle;
	int commitCycle;
	int isMisPredictedBranch;
	uint64_t addressForMemoryOp;
};

struct robdqueue
{
	struct robnode *front;
	struct robnode *rear;
};

struct robnode
{
    struct opData op;
	struct robnode *link ;
};


void initdqueuerob ( struct robdqueue * ) ;
void addqatendrob ( struct robdqueue *, struct opData item ) ;
struct opData delqatbegrob ( struct robdqueue * ) ;

/* initializes elements of ROB structure */
void initdqueuerob ( struct robdqueue *p )
{
    p ->  front = p -> rear = NULL ;
}


/* adds item at the end of dqueue */
void addqatendrob ( struct robdqueue *p, struct opData item )
{
    struct robnode *temp ;

    temp = ( struct robnode * ) malloc ( sizeof ( struct robnode )  );
    temp -> op = item ;
    temp -> link = NULL ;

    if ( p -> front == NULL )
        p -> front = temp ;
    else
        p -> rear -> link = temp ;
    p -> rear = temp ;
}

/* deletes item from begining of ROB dqueue */
struct opData delqatbegrob ( struct robdqueue *p )
{
    struct robnode *temp = p -> front ;
    struct opData item ;
    if ( temp == NULL )
    {
        printf ( "\nQueue is empty." ) ;
        return item;
    }
    else
    {
        temp = p -> front ;
        item = temp -> op ;
        p -> front = temp -> link ;
        free ( temp ) ;

        if ( temp == NULL )
            p -> rear = NULL ;
        return ( item ) ;
    }
}

int countrob ( struct robdqueue dq )
{
    int c = 0 ;
    struct robnode *temp = dq.front ;

    while ( temp != NULL )
    {
        temp = temp -> link ;
        c++ ;
    }

    return c ;
}

bool isReady(int s1,int s2,int s3,int isLoad,int64_t microOpCount,int64_t currentCycle,struct robdqueue robdq,uint64_t addressForMemoryOp)
{
	if((s1 != -1 && scoreBoard[s1] != 0) || (s2 != -1 && scoreBoard[s2] != 0) || (s3 != -1 && scoreBoard[s3] != 0))
		return false;
	else if(isLoad == 1)
	{
		if(countrob(robdq) > 0){
			struct robnode *temp = robdq.front;
			while ( temp != NULL )
		    {
				if(temp->op.isStore == 1 && temp->op.microOpCount < microOpCount && !(temp->op.doneCycle <= currentCycle && temp->op.doneCycle != -1))
					if(addressForMemoryOp == temp->op.addressForMemoryOp)
					return false;
				temp = temp -> link;
			}
		}
	}
	else
		return true;
	
	return true;
	/*if(s1 != -1 && s2 != -1 && s3 != -1)
	{
		if(scoreBoard[s1] == 0 && scoreBoard[s2] == 0 && scoreBoard[s3] == 0)
			return true;
		else
			return false;
	}
	return false;*/
}	
	






void simulate(FILE* inputFile, struct dqueue dq,struct robdqueue robdq, int N, int64_t predictorSize)
{
  int32_t microOpCount;
  uint64_t instructionAddress;
  int32_t sourceRegister1;
  int32_t sourceRegister2;
  int32_t destinationRegister;
  char conditionRegister;
  char TNnotBranch;
  char loadStore;
  int64_t immediate;
  uint64_t addressForMemoryOp;
  uint64_t fallthroughPC;
  uint64_t targetAddressTakenBranch;
  char macroOperation[12];
  char microOperation[23];

  int64_t totalMicroops = 0;
  int64_t totalMacroops = 0;

  
  int32_t traceIndex = 1;
  int maptable[REGSIZE];
  initdqueue ( &dq );
  
  for(int i=50;i<REGSIZE;i++)
  addqatend(&dq,i);
  
  struct opData commitedOpData;
  struct opData currentOpData;
  int64_t currentCycle = 0;
  int64_t insnNumber = 1;
  int issueCounter = 0;
  int latency = 1;
  int eof = 0;
  char predictedState = 'N';
  int indexForBranchPrediction = 0;
  int64_t history = 0;
  int fetchReady = 0;
  
  int64_t tagAndIndex = 0;
  int64_t index = 0;
  int64_t tag = 0;
  int64_t cache[8192][2];
  int64_t LRU[8192] = {0};
  int64_t b = 64;
  
  for(int i=0;i<REGSIZE;i++)
  {
	  maptable[i]=i;
	  scoreBoard[i]=0;
  }
  
  
  printf("Processing trace...\n");
  
  while (true) {
  //while(currentCycle <= 25){
    
	if(countrob(robdq) > 0)
	{
		//---------------------------------------------------------------------------------------------------------------------
		// For Commit Stage 
		for (int i=0; i<N; i++){
			
			if(robdq.front->op.doneCycle <= currentCycle && robdq.front->op.doneCycle != -1)
			{
				commitedOpData = delqatbegrob(&robdq);
				//printf("%" PRIi64": %d %d %d %" PRIi64", p%d p%d p%d p%d p%d \n" ,commitedOpData.microOpCount,commitedOpData.fetchCycle,commitedOpData.issueCycle,commitedOpData.doneCycle,currentCycle,commitedOpData.sourceRegs[0],commitedOpData.sourceRegs[1],commitedOpData.sourceRegs[2],commitedOpData.destinationRegs[0],commitedOpData.destinationRegs[1]);
			}
			if(countrob(robdq) == 0)
				break;
		}
		
		
	}
	//if(traceFinished == 1)
	if(eof == 1 && countrob(robdq) == 0)
	{
		currentCycle++;
		break;			
	}

	 //---------------------------------------------------------------------------------------------------------------------
	 // For Issue Stage
	 if(countrob(robdq) > 0){
		issueCounter = 0;
		
		struct robnode *temp = robdq.front;
		while ( temp != NULL )
	    {
	  	    if(temp->op.isIssued == 0 && isReady(temp->op.sourceRegs[0],temp->op.sourceRegs[1],temp->op.sourceRegs[2],temp->op.isLoad,temp->op.microOpCount,currentCycle,robdq,temp->op.addressForMemoryOp))
			{
				if(temp->op.isLoad == 1)
				{
					
				    tagAndIndex = (temp->op.addressForMemoryOp) >> 6;
                    index = tagAndIndex % b;
                    tag = tagAndIndex >> 6;
					
		            //printf("cache vals: %" PRIi64 " and %" PRIi64 "\n" PRIi64,cache[index][0],cache[index][1]);
					//printf("tag: %" PRIi64 "\n",tag);
					
					if(cache[index][0] == tag)
		            {
		                if(LRU[index] == 0)
		                    LRU[index] = 1;
						latency = 4;
		            }
		            else if(cache[index][1] == tag)
		            {
		                if(LRU[index] == 1)
		                    LRU[index] = 0;
						latency = 4;
		            }
		            else
		            {
						latency = 4+7; // 7 is the miss penalty
		                cache[index][LRU[index]] = tag;
		                if(LRU[index] == 0)
		                    LRU[index] = 1;
		                else
		                    LRU[index] = 0;
					}
					//latency = 4;
				}
				else
				latency = 1;

				temp->op.isIssued = 1;
				temp->op.issueCycle = currentCycle;
				temp->op.doneCycle = currentCycle + latency;
				
				if(temp->op.isMisPredictedBranch == 1)
					fetchReady = latency + 3; // 3 is mis-prediction restart penalty
				if(temp->op.destinationRegs[0] != -1)
				  scoreBoard[temp->op.destinationRegs[0]] = latency;
				if(temp->op.destinationRegs[1] != -1)
				  scoreBoard[temp->op.destinationRegs[1]] = latency;
				
			    issueCounter++;
			    if (issueCounter == N)
			      break;  
			}
			temp = temp -> link ;
	    }
	}
	//---------------------------------------------------------------------------------------------------------------------
	// For Fetch and Register Renaming
	for(int i=0;i<N;i++){
		
		if(fetchReady > 0)
		{
			fetchReady--;
			break;
		}
		if(fetchReady == -1)
			break;

		//assert(fetchReady == 0);
		
		
		if(countrob(robdq) == ROBSIZE)
			break;
		else if(eof != 1)
		{
		   	// Reading a micro-op 
		    int result = fscanf(inputFile, 
		                        "%" SCNi32
		                        "%" SCNx64 
		                        "%" SCNi32
		                        "%" SCNi32
		                        "%" SCNi32
		                        " %c"
		                        " %c"
		                        " %c"
		                        "%" SCNi64
		                        "%" SCNx64
		                        "%" SCNx64
		                        "%" SCNx64
		                        "%11s"
		                        "%22s",
		                        &microOpCount,
		                        &instructionAddress,
		                        &sourceRegister1,
		                        &sourceRegister2,
		                        &destinationRegister,
		                        &conditionRegister,
		                        &TNnotBranch,
		                        &loadStore,
		                        &immediate,
		                        &addressForMemoryOp,
		                        &fallthroughPC,
		                        &targetAddressTakenBranch,
		                        macroOperation,
		                        microOperation);
                    
		    if (result == EOF) {
				eof = 1;
				break;
		    }

		    if (result != 14) {
		      fprintf(stderr, "Error parsing trace at line %" PRIi64 "\n", totalMicroops);
		      abort();
		    }

		    // For each micro-op
		    totalMicroops++;

		    // For each macro-op:
		    if (microOpCount == 1) {
		      totalMacroops++;
		    }
		
			currentOpData.microOpCount = insnNumber;
			insnNumber++;
			traceIndex++;
			if(sourceRegister1 != -1)
			{
				currentOpData.sourceRegs[0] = maptable[sourceRegister1];
				//printf("source Reg: %d\n",sourceRegister1);
				//printf("value in maptable: %d\n",maptable[sourceRegister1]);
				currentOpData.regReady[0] = scoreBoard[currentOpData.sourceRegs[0]];
			}
			else
				currentOpData.sourceRegs[0] = -1;
			
			if(sourceRegister2 != -1)
			{
				currentOpData.sourceRegs[1] = maptable[sourceRegister2];
				//printf("source reg: %d\n",sourceRegister2);
				//printf("value in maptable:  %d\n",maptable[sourceRegister2]);				
				currentOpData.regReady[1] = scoreBoard[currentOpData.sourceRegs[1]];	
			}
			else
				currentOpData.sourceRegs[1] = -1;
			
			if(conditionRegister == 'R')
			{
				currentOpData.sourceRegs[2] = maptable[49];
				currentOpData.regReady[2] = scoreBoard[currentOpData.sourceRegs[2]];
			}
			else
				currentOpData.sourceRegs[2] = -1;
			
			if(destinationRegister != -1)
			{
				int registerFreed = maptable[destinationRegister];
				maptable[destinationRegister] = delqatbeg(&dq);
				addqatend(&dq,registerFreed);
				currentOpData.destinationRegs[0] = maptable[destinationRegister];
				scoreBoard[currentOpData.destinationRegs[0]] = -1;
			}
			else
				currentOpData.destinationRegs[0] = -1;
		   
		    if(conditionRegister == 'W')
			{
				int registerFreed = maptable[49];
				maptable[49] = delqatbeg(&dq);
				addqatend(&dq,registerFreed);
	
				currentOpData.destinationRegs[1] = maptable[49];
				scoreBoard[currentOpData.destinationRegs[1]] = -1;
			}
			else
				currentOpData.destinationRegs[1] = -1;
			
			if(loadStore == 'L')
				currentOpData.isLoad = 1;
			else
				currentOpData.isLoad = 0;
			
			if(loadStore == 'S')
				currentOpData.isStore = 1;
			else
				currentOpData.isStore = 0;
			
			currentOpData.isIssued = 0;
			currentOpData.fetchCycle = currentCycle;
			currentOpData.issueCycle = -1;
			currentOpData.doneCycle = -1;
			currentOpData.commitCycle = -1;
			
		    if(conditionRegister == 'R' && TNnotBranch != '-')
		    {
			   	indexForBranchPrediction = instructionAddress ^ history;
		        indexForBranchPrediction = indexForBranchPrediction % (predictorSize);
        
		        if(tableCounter[indexForBranchPrediction] == 'n' || tableCounter[indexForBranchPrediction] == 'N')
				predictedState = 'N';
				else
				predictedState = 'T';
	
				if(predictedState != TNnotBranch)
				{
					//totalIncorrectPredictions++;
					fetchReady = -1;
					currentOpData.isMisPredictedBranch = 1;
					//printf("incorrect");
					if(TNnotBranch == 'T' && tableCounter[indexForBranchPrediction] == 'N')
						tableCounter[indexForBranchPrediction] = 'n';
					else if(TNnotBranch == 'T' && tableCounter[indexForBranchPrediction] == 'n')
						tableCounter[indexForBranchPrediction] = 't';
					else if(TNnotBranch == 'N' && tableCounter[indexForBranchPrediction] == 'T')
						tableCounter[indexForBranchPrediction] = 't';
					else if(TNnotBranch == 'N' && tableCounter[indexForBranchPrediction] == 't')
						tableCounter[indexForBranchPrediction] = 'n';
				}
				else
				{
					if(tableCounter[indexForBranchPrediction] == 'n')
						tableCounter[indexForBranchPrediction] = 'N';
					else if(tableCounter[indexForBranchPrediction] == 't')
						tableCounter[indexForBranchPrediction] = 'T';
					
					//fetchReady = 0;
					currentOpData.isMisPredictedBranch = 0;
				}
		        history = history << 1;
				if(history > 65536)
		        history = history % 65536;

		        if(TNnotBranch == 'T')
				history = history | 1;
		    }
			else
				currentOpData.isMisPredictedBranch = 0;
			
			
			currentOpData.addressForMemoryOp = addressForMemoryOp;
			addqatendrob(&robdq,currentOpData);
			
			if(TNnotBranch == 'T')
				break;
		}
	} // End of For Loop
	//---------------------------------------------------------------------------------------------------------------------
	// Advance to Next Cycle 
	currentCycle++;
	for(int i=0;i<REGSIZE;i++){
		if(scoreBoard[i] > 0)
			scoreBoard[i] = scoreBoard[i] - 1;
	}	
		
  } // End of While Loop
  
  printf("Processed %" PRIi64 " trace records.\n", totalMicroops);
  printf("Micro-ops: %" PRIi64 "\n", totalMicroops);
  printf("Macro-ops: %" PRIi64 "\n", totalMacroops);
  printf("totalCycles: %" PRIi64 "\n",currentCycle);	
}


int main() 
{
	FILE *inputFile;
	struct dqueue dq ;
    initdqueue ( &dq ) ;

	struct robdqueue robdq;
	initdqueuerob(&robdq);
	
	inputFile = fopen("sjeng-10M.trace", "r");
	
	for(int i=0;i<65536;i++)
		tableCounter[i] = 'N';
	
	simulate(inputFile,dq,robdq,8,65536);
	return 0;
}
