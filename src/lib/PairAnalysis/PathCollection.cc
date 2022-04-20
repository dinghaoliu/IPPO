#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/Dominators.h>

#include <unistd.h>
#include <thread>
#include <mutex>
#include <omp.h>
#include <time.h>

#include "PairAnalysis.h"

using namespace llvm;

//#define DEBUG_PATH_COLLECTION_RESULT

//Warshall Algorithm
bool PairAnalysisPass::updateConnectGraph(ConnectGraph &connectGraph,
    vector<BasicBlock*> globalblockset){

    bool changetag = false;

    if(connectGraph.empty())
        return changetag;
    
    //Searching backwards is faster
    for(auto rit = connectGraph.rbegin(); rit != connectGraph.rend();rit++){
        Blockpair blockpair = rit->first;
        BasicBlock* firstbb = blockpair.first;
        BasicBlock* secondbb = blockpair.second;
        if(rit->second && firstbb != secondbb){
            
            for(auto it = globalblockset.begin(); it != globalblockset.end();it++){

                BasicBlock* firstbb_in = *it;

                Blockpair blockpair_update(firstbb_in,firstbb);
                if(connectGraph[blockpair_update]){
                    Blockpair blockpair_update2(firstbb_in,secondbb);
                    if(connectGraph[blockpair_update2]==false)
                        changetag = true;
                    connectGraph[blockpair_update2]=true;
                }   
            }
        }
    }
    return changetag;
}

//Current assume that CFG has no loop
//ConnectGraph is used to check if a block is reachable for another
void PairAnalysisPass::initConnectGraph(Function *F,ConnectGraph &connectGraph,
    vector<BasicBlock*> globalblockset,
    EdgeIgnoreMap edgeIgnoreMap){

    connectGraph.clear();
    if(!F)
        return;
    
    vector<vector<BasicBlock*>> CG;
    CG.clear();

    //init
    for (Function::iterator b1 = F->begin(), e1 = F->end();
		b1 != e1; ++b1) {
            
		BasicBlock *BB1 = &*b1;

        for(Function::iterator b2 = F->begin(), e2 = F->end(); 
            b2 != e2; ++b2){

            BasicBlock *BB2 = &*b2;
            Blockpair blockpair(BB1,BB2);
            pair<Blockpair, bool> value(blockpair,false);

            if(BB1==BB2){
                value.second = true;
            }
            
            connectGraph.insert(value);
        }
        
        //succ check
        auto TI = BB1->getTerminator();
        if(TI->getNumSuccessors() == 0)
            continue;
        
        for(BasicBlock *Succ : successors(BB1)){
            CFGEdge edge = make_pair(TI,Succ);
            if(edgeIgnoreMap.count(edge) != 0){
                continue;
            }

            Blockpair blockpair(BB1,Succ);
            connectGraph[blockpair] = true;
        }
        
    }

    while(updateConnectGraph(connectGraph,globalblockset)){
        //OP << "Round again\n";
    }
}

bool PairAnalysisPass::checkBlockAToB_Version2(BasicBlock*a, BasicBlock *b,
    ConnectGraph connectGraph){
    
    if(!a || !b){
        return false;
    }

    Blockpair blockpair(a,b);
    return connectGraph[blockpair];
}

//Check if a basic block is a branch block with the help of edgeIgnoreMap
bool PairAnalysisPass::checkBranchWithMap(BasicBlock *bb, EdgeIgnoreMap edgeIgnoreMap){

    if(!bb)
        return false;

    auto TI = bb->getTerminator();
    int NumSucc = TI->getNumSuccessors();

    if(NumSucc<2)
        return false;

    set<BasicBlock *> nextblockset;
    nextblockset.clear();
    for(BasicBlock* Succ : successors(bb)){
        nextblockset.insert(Succ);
    }

    if(nextblockset.size()<2)
        return false;
    
    for(auto it = nextblockset.begin(); it != nextblockset.end();it++){
        BasicBlock* succblock = *it;
        CFGEdge edge = make_pair(TI,succblock);

        if(edgeIgnoreMap.count(edge)!=0){
            NumSucc--;
        }
    }

    if(NumSucc>1)
        return true;
    else
        return false;
}

//Check if a basic block is a merge block with the help of edgeIgnoreMap
bool PairAnalysisPass::checkMergeWithMap(BasicBlock *bb, EdgeIgnoreMap edgeIgnoreMap){
    if(!bb)
        return false;

    int NumPred = pred_size(bb);

    if(NumPred<2)
        return false;

    set<BasicBlock *> predblockset;
    predblockset.clear();

    for(BasicBlock *PredBB : predecessors(bb)){
        predblockset.insert(PredBB);
    }

    if(predblockset.size()<2)
        return false;
    
    for(auto it = predblockset.begin(); it != predblockset.end();it++){
        BasicBlock* predblock = *it;
        auto TI = predblock->getTerminator();
        CFGEdge edge = make_pair(TI,bb);

        if(edgeIgnoreMap.count(edge)!=0){
            NumPred--;
        }
    }

    if(NumPred>1)
        return true;
    else
        return false;
}

void PairAnalysisPass::addSelfLoopEdges(Function *F,
    EdgeIgnoreMap &edgeIgnoreMap){

    if(!F)
        return;
    
    for(Function::iterator b = F->begin(); 
        b != F->end(); b++){

        BasicBlock * bb = &*b;
        Instruction *TI =bb->getTerminator();
        int NumSucc = TI->getNumSuccessors();

        if(NumSucc == 0)
            continue;

        for(BasicBlock *Succ : successors(bb)){
            if(Succ == bb){
                CFGEdge edge = make_pair(TI,Succ);
                pair<CFGEdge,int> value(edge,1);
                edgeIgnoreMap.insert(value);
            }
        }
    }

    return;
}

//Initialize indegreeMap
void PairAnalysisPass::initIndegreeMap(Function *F, 
    std::map<BasicBlock*, int> &indegreeMap,
    EdgeIgnoreMap edgeIgnoreMap){

    indegreeMap.clear();

    if(!F)
        return;
    
    for(Function::iterator b = F->begin(); 
        b != F->end(); b++){

        BasicBlock * bb = &*b;

        int NumPred = pred_size(bb);
        
        if(NumPred>1){

            set<BasicBlock *> blockset;
            blockset.clear();

            for (BasicBlock *PredBB : predecessors(bb)){
                blockset.insert(PredBB);
            }

            NumPred = blockset.size();

            //BasicBlock* curbb;
            //for (BasicBlock *PredBB : predecessors(bb)){
            for (auto it = blockset.begin(); it != blockset.end();it++){
                BasicBlock* PredBB = *it;
                auto predTI = PredBB->getTerminator();

                //Ignore edges in edgeIgnoreMap
                CFGEdge edge = make_pair(predTI,bb);
                if(1 == edgeIgnoreMap.count(edge)){
                    NumPred--;
                }

                //Ignore loop that a block pointing to itself
                if(bb == PredBB){
                    NumPred--;
                }
            }
            blockset.clear(); 
        }//end if

        pair<BasicBlock*, int>value(bb,NumPred);
        indegreeMap.insert(value);        

    }
}

//Initialize normalEdgeMap
void PairAnalysisPass::initNormalEdgeMap(Function *F,
    EdgeIgnoreMap &normalEdgeMap,
    EdgeIgnoreMap errEdgeMap){

    normalEdgeMap.clear();

    //Build a CFG with only error edges    
    set<CFGEdge> targetEdgeSet;
    queue<CFGEdge> edgequeue;
    targetEdgeSet.clear();
    set<BasicBlock*> predBlockSet;
    predBlockSet.clear();
    set<BasicBlock*> succBlockSet;
    succBlockSet.clear();

    for(auto it = errEdgeMap.begin(); it != errEdgeMap.end();it++){
        targetEdgeSet.insert(it->first);
        CFGEdge edge = it->first;
        Instruction *TI = edge.first;
        BasicBlock *predBB = TI->getParent();
        BasicBlock *succBB = edge.second;
        predBlockSet.insert(predBB);
        succBlockSet.insert(succBB);
        edgequeue.push(edge);
    }

    
    while(!edgequeue.empty()){
        CFGEdge topedge = edgequeue.front();
        edgequeue.pop();

        Instruction *TI = topedge.first;
        
        BasicBlock *predBB = TI->getParent();
        BasicBlock *succBB = topedge.second;
        Instruction *succblockTI = succBB->getTerminator();

        //First resolve the predBB
        //If predBB is the beginning block of this function, do nothing
        //Otherwise, find a path leading to the beginning block
        if(pred_size(predBB) != 0){

            //Current edge cannot be accessed by any other edges
            if(succBlockSet.count(predBB) == 0){

                BasicBlock *predblock = NULL;
                set<BasicBlock*> predblockset;
                predblockset.clear();
                for (BasicBlock *predbb : predecessors(predBB)){
                    if(predbb == predBB)
                        continue;
                    predblockset.insert(predbb);
                    if(succBlockSet.count(predbb) != 0){
                        predblock = predbb;
                        break;
                    }
                }

                if(predblock == NULL){
                    if(predblockset.size() == 1)
                        predblock =*(predblockset.begin());
                    
                    //We need to select one from predblockset to extend the graph
                    //Always choose the longest path
                    else {
                        predblock = findBottomBlock(predblockset);
                        if(predblock == NULL)
                            predblock = *(predblockset.begin());
                    }
                }

                //for (BasicBlock *predblock : predecessors(predBB)){
                //    if(predblock != predBB){
                        auto predBB_TI = predblock->getTerminator();
                        CFGEdge edge = make_pair(predBB_TI,predBB);
                        edgequeue.push(edge);
                        targetEdgeSet.insert(edge);
                        succBlockSet.insert(predBB);
                        predBlockSet.insert(predblock);
                        //OP <<"Pre Add: "<< getBlockName(predblock) << " -> " << getBlockName(predBB)<<"\n";
                //        break;
                //    }
                //}

            }
        }

        //Next resolve the succBB
        //If succBB is the end block of this function, do nothing
        //Otherwise, find a path leading to the end block
        if(succblockTI->getNumSuccessors() != 0){

            //Current block has not been added to the existing graph
            if(predBlockSet.count(succBB) == 0){
                auto succBB_TI = succBB->getTerminator();
                BasicBlock *succblock = NULL;
                set<BasicBlock*> succblockset;
                succblockset.clear();
                for(BasicBlock *Succ : successors(succBB)){
                    if(Succ == succBB)
                        continue;
                    succblockset.insert(Succ);
                }

                //Only one possible path
                if(succblockset.size() == 1)
                    succblock = *(succblockset.begin());
                else {
                    succblock = findTopBlock(succblockset);
                }
                
                if(succblock == NULL && succblockset.size() != 0) {
                    succblock = *(succblockset.begin());
                }

                if(succblock == NULL)
                    continue;

                CFGEdge edge = make_pair(succBB_TI,succblock);
                edgequeue.push(edge);
                targetEdgeSet.insert(edge);
                succBlockSet.insert(succblock);
                predBlockSet.insert(succBB);
            }
        }
    }

    for(Function::iterator bb = F->begin(); 
        bb != F->end(); bb++){
        
        BasicBlock * B = &*bb;

        auto TI = B->getTerminator();
        for(BasicBlock *Succ : successors(B)){
            CFGEdge edge = make_pair(TI,Succ);
            if(targetEdgeSet.count(edge) == 0){
                pair<CFGEdge,int> value(edge,1);
                normalEdgeMap.insert(value);
            }
        }
    }

}

//Recursively find paths from a basic block
void PairAnalysisPass::recurFindPaths(std::map<BasicBlock *, SinglePath> &branchvisitMap,
    EdgeIgnoreMap &edgeIgnoreMap,
    std::map<BasicBlock*, int> &indegreeMap,
    BasicBlock *bb,                          //Record current basic block
    ConnectGraph &connectGraph,     
    SinglePath &curpath,                      //Record current path (from branch)
    std::vector<PathPairs> &PathGroup){      //Record current path pair group
    
    if(!bb)
        return;
    
    SinglePath returnpath;

    //Transform BasicBlock to CompoundBlock
    CompoundBlock CB;
    CB.BB = bb;
    findFunctionCalls(bb,CB.CallFunctionSet);

    auto TI = bb->getTerminator();
    int NumSucc = TI->getNumSuccessors();
    int NumPred = indegreeMap[bb];

    #ifdef DEBUG_PATH_COLLECTION_RESULT
    OP<< "Current resolving block: block-"<<getBlockName(CB.BB)<<" ";

    if(curpath.getPathLength()==0){
        OP << "No path is on collection\n";
    }
    else{
        OP << "A path is on collection ";
        BasicBlock * toppathbb = curpath.CBChain[0].BB;
        OP << "-start from "<<getBlockName(toppathbb)<<"\n";
    }
    #endif

    /////////////////////////////////////////////////////////////////////
    //Check the predblock (Merge check)
    /////////////////////////////////////////////////////////////////////

    //This block is a potential merge block, return
    //Finish path collection once find a merge block
    if(NumPred>1){
        CB.merge = true;

        //There is a path from a branch point
        if(curpath.getPathLength()>0){
            if(curpath.CBChain.back().BB != bb)
                curpath.CBChain.push_back(CB);
            curpath.mergeBlock = CB;
        }
        return;
    }
    
    /////////////////////////////////////////////////////////////////////
    //Check the succblock (Branch check)
    /////////////////////////////////////////////////////////////////////

    //This path is traveled before
    if(branchvisitMap.count(bb) == 1){
        #ifdef DEBUG_PATH_COLLECTION_RESULT
        OP << "This path is traveled before " << "-curbb is block-" <<getBlockName(bb) <<"\n";
        #endif

        //One path is on collection, resolve the curpath
        if(curpath.getPathLength()!=0){
            curpath.CBChain.insert(curpath.CBChain.end(),branchvisitMap[bb].CBChain.begin(),branchvisitMap[bb].CBChain.end());
            curpath.mergeBlock = branchvisitMap[bb].CBChain.back();
            return;
        }

        //No path is on collection, then find the end of collected path
        BasicBlock * endblock = branchvisitMap[bb].CBChain.back().BB;
        
        //This is a return block
        if(checkReturnBlock(endblock,edgeIgnoreMap)){
            return;
        }

        //Not a return block, keep recurfind
        recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,endblock,connectGraph,curpath,PathGroup);

        return;
    }

    Branch_Check:

    //The block is the end of this path
    if(NumSucc == 0){

        //There is a curpath on collection
        if(curpath.getPathLength()!=0){
            curpath.CBChain.push_back(CB);
            curpath.mergeBlock = CB;
        }
        return;
    }

    //The block has only one successor (maybe inside a loop, thus we ned to remove all loops)
    else if(NumSucc == 1){

        //Get the succblock
        BasicBlock *succblock = TI->getSuccessor(0);

        //There is a curpath on collection
        if(curpath.getPathLength()!=0){
            curpath.CBChain.push_back(CB);
        }

        //The successor edge is ignored
        CFGEdge edge = make_pair(TI,succblock);
        if(1 == edgeIgnoreMap.count(edge)){
            curpath.CBChain.push_back(CB);
            curpath.mergeBlock = CB;
            return;
        }

        recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,succblock,connectGraph,curpath,PathGroup);

    }

    //The block has multiple branch successors
    //then this block is a potential branch block (start of paths)
    else{

        CB.branch = true;

        //Collect set of succblock to remove repeated block 
        set<BasicBlock *> nextblockset;
        nextblockset.clear();

        for(unsigned i = 0; i != NumSucc; i++){
            BasicBlock *succblock = TI->getSuccessor(i);

            //Ignore edges in edgeIgnoreMap
            CFGEdge edge = make_pair(TI,succblock);

            if(1 == edgeIgnoreMap.count(edge)){
                continue;
            }
            
            //The succblock pointing to current block is forbidden (loop)
            if(succblock == bb)
                continue;

            nextblockset.insert(succblock);
        }

        //Only one valid succblock
        if(nextblockset.size()==1){

            //There is a curpath on collection
            if(curpath.getPathLength()!=0){
                if(curpath.CBChain.back().BB != bb)
                    curpath.CBChain.push_back(CB);
            }
            recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,*nextblockset.begin(),connectGraph,curpath,PathGroup);
            return;
        }

        //No valid succblock
        else if(nextblockset.empty()){

            //There is a curpath on collection
            if(curpath.getPathLength()!=0){
                curpath.CBChain.push_back(CB);
                curpath.mergeBlock = CB;
            }
            return;
        }

        //Multiple valid succblocks
        //This is the start of new path pairs
        else{

            //Build new pathpairs 
            PathPairs curpathpairs;
            curpathpairs.startBlock = CB;

            //Collect paths for each succblock (usually two paths)
            for(auto it = nextblockset.begin(); it != nextblockset.end();it++){
                BasicBlock *succblock = *it;

                //Build single path for each branch
                SinglePath Path;
                Path.startBlock = CB;
                Path.CBChain.push_back(CB); //Note: push_back is a kind of copy

                recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,succblock,connectGraph,Path,PathGroup);
                
                //Finish path collection once find a merge block
                curpathpairs.Paths.push_back(Path);
                curpathpairs.mergeBlocks.insert(Path.mergeBlock);

                Path.CBChain.clear();
            }//collect finished
            
            MergeCheck:

            if(!curpathpairs.UpdatedMergeSet()){
                OP << "Error: UpdatedMergeSet Wrong details!!!\n";
            }

            //Add path pairs to the path group
            //All path pairs in the same group have the same branch block
            PathGroup.push_back(curpathpairs);

            #ifdef DEBUG_PATH_COLLECTION_RESULT
            //Print collected paths of curpathpairs
            for(auto i = curpathpairs.Paths.begin(); i != curpathpairs.Paths.end(); i++){
                printSinglePath(*i);
            }
            #endif

            //Choose the next start block

            ///////////////////////////////////////////////////////////////////////////////////////////////////////////
            //All paths in curpathpairs merge at one block
            //This is the case we want.
            ///////////////////////////////////////////////////////////////////////////////////////////////////////////
            if(curpathpairs.mergeBlocks.size()==1){

                #ifdef DEBUG_PATH_COLLECTION_RESULT
                OP<<"--One merge block!"<< "--current-"<< getBlockName(CB.BB) << "\n";  
                #endif

                //Update indegreeMap
                BasicBlock* mergeblock = curpathpairs.Paths[0].mergeBlock.BB;
                indegreeMap[mergeblock] -= curpathpairs.getPathNum();
                indegreeMap[mergeblock]++;

                //There is a curpath on collection
                if(curpath.getPathLength()!=0){

                    #ifdef DEBUG_PATH_COLLECTION_RESULT
                    OP<<"A curpath is on collection\n";
                    #endif

                    //OP << "Inside One merge block, merge start at block-"<<getBlockName(curpathpairs.startBlock.BB)<<"\n";
                    //Pick only one path from the branches to continue??

                    //Choose the minest path to represent current collected path pair
                    //Find a longest path as the chosen path
                    int index = -1;
                    int maxlength = 0;
                    for(int it = 0; it != curpathpairs.getPathNum(); it++){
                        int curlength = curpathpairs.Paths[it].getPathLength();
                        if(maxlength < curlength){
                            maxlength = curlength;
                            index = it;
                        }
                    }

                    if(returnpath.getPathLength()!=0){
                        
                        curpath.CBChain.insert(curpath.CBChain.end(),returnpath.CBChain.begin(),returnpath.CBChain.end());
                        curpath.mergeBlock = returnpath.CBChain.back();
                        #ifdef DEBUG_PATH_COLLECTION_RESULT
                        OP<<"(A returnpath is on collection): ";
                        printSinglePath(curpath);
                        #endif
                        if(branchvisitMap.count(curpathpairs.Paths[index].CBChain[0].BB) == 0){
                            branchvisitMap[curpathpairs.Paths[index].CBChain[0].BB] = curpathpairs.Paths[index];
                            #ifdef DEBUG_PATH_COLLECTION_RESULT
                            OP << "++BranchvisitMap updated, start from: "<< getBlockName(curpathpairs.Paths[index].CBChain[0].BB) <<"\n";
                            OP << "++Added path: ";
                            printSinglePath(curpathpairs.Paths[index]);
                            #endif
                        }
                        return;
                    } 


                    //Since all paths merge at the same block, choose the longest one
                    curpath.CBChain.insert(curpath.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());

                    //Update branchvisitMap
                    if(branchvisitMap.count(curpathpairs.Paths[index].CBChain[0].BB) == 0){
                        branchvisitMap[curpathpairs.Paths[index].CBChain[0].BB] = curpathpairs.Paths[index];
                        #ifdef DEBUG_PATH_COLLECTION_RESULT
                        OP << "++BranchvisitMap updated, start from: "<< getBlockName(curpathpairs.Paths[index].CBChain[0].BB) <<"\n";
                        OP << "++Added path: ";
                        printSinglePath(curpathpairs.Paths[index]);
                        #endif
                    }

                    curpath.CBChain.pop_back();              
                    recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,mergeblock,connectGraph,curpath,PathGroup);
                    return;
                }

                #ifdef DEBUG_PATH_COLLECTION_RESULT
                OP<<"No curpath is on collection\n";
                #endif

                //There is no curpath on collection
                
                //This block has already added to the path
                //Update related variables
                CB = *(curpathpairs.mergeBlocks.begin());
                BasicBlock *succblock = CB.BB;

                //This condition will never triggered
                //Otherwise there is an error 
                if(!succblock){
                    OP<<"Err: No succblock "<<"\n";
                    //Do nor return, let it go and crash
                }                

                TI = succblock->getTerminator();
                NumSucc = TI->getNumSuccessors();
                goto Branch_Check;
            }

            ///////////////////////////////////////////////////////////////////////////////////////////////////////////
            //Paths in curpathpairs end at different blocks,
            //which means they do not merge at all
            ///////////////////////////////////////////////////////////////////////////////////////////////////////////
            else if(curpathpairs.mergeBlocks.size()>1){

                #ifdef DEBUG_PATH_COLLECTION_RESULT
                OP<<"--More than one merge block!"<< "--current-"<< getBlockName(CB.BB) << "\n";
                #endif

                //Abandon current collection
                PathGroup.pop_back();
                
                ///////////////////////////////////////////////////////////////////////////////////////////////
                //Recover useful info from curpathpairs (this is popped, but still contains sth useful)
                map<BasicBlock *, set<int> > recoverset;
                for(int i = 0; i<curpathpairs.getPathNum(); i++){
                    BasicBlock *mergebbi = curpathpairs.Paths[i].mergeBlock.BB;
                    recoverset[mergebbi].insert(i);
                }

                bool recovertag = false;

                for(auto i = recoverset.begin(); i != recoverset.end();i++){
                    //Execute recovery
                    if(i->second.size()>1){
                        recovertag = true;
                        BasicBlock * mergeblock = i->first;
                        indegreeMap[mergeblock] -= i->second.size();
                        indegreeMap[mergeblock]++;

                        PathPairs recoverpathpair;
                        recoverpathpair.startBlock = curpathpairs.Paths[0].startBlock;

                        for(auto j = i->second.begin(); j!=i->second.end();j++){
                            recoverpathpair.Paths.push_back(curpathpairs.Paths[*j]);
                        }

                        CompoundBlock CB_recover_merge;
                        CB_recover_merge.BB = i->first;
                        recoverpathpair.mergeBlocks.insert(CB_recover_merge);

                        PathGroup.push_back(recoverpathpair);
                    }
                }
                //end recover
                ///////////////////////////////////////////////////////////////////////////////////////////////

                //check if all of these mergeblocks are return blocks
                if(!recovertag){
                    //OP << "Not recover\n";
                    bool allreturn = true;
                    for(auto i = recoverset.begin(); i != recoverset.end();i++){
                        BasicBlock * mergebb = i->first;
                        if(!checkReturnBlock(mergebb,edgeIgnoreMap)){
                            allreturn = false;
                            break;
                        }
                    }

                    if(allreturn){

                        #ifdef DEBUG_PATH_COLLECTION_RESULT
                        OP << "All of these mergeblocks are return blocks!\n";
                        #endif
                        //There is a curpath on collection
                        if(curpath.getPathLength()!=0){
                            
                            //There is a returnpath on collection
                            if(returnpath.getPathLength()!=0){

                                #ifdef DEBUG_PATH_COLLECTION_RESULT
                                OP << "A returnpath is on collection: ";
                                printSinglePath(returnpath);
                                #endif
                                
                                curpath.CBChain.insert(curpath.CBChain.end(),returnpath.CBChain.begin(),returnpath.CBChain.end());
                                curpath.mergeBlock = returnpath.CBChain.back();
                                return;
                            }
                            
                            //OP << "No returnpath is on collection\n";
                            //OP << "There is a curpath on collection ";

                            //Choose the end block with more than one indegree
                            int index = 0;
                            for(auto i = recoverset.begin(); i != recoverset.end();i++){
                                BasicBlock * mergebb = i->first;
                                if(indegreeMap[mergebb]>1)
                                    index = *(i->second.begin());
                            }

                            //Choose the first one as the path block
                            //Todo: find a better way to resolve this condition
                            curpath.mergeBlock = curpathpairs.Paths[index].mergeBlock;
                            curpath.CBChain.insert(curpath.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());
                            return;
                        }

                        BasicBlock *succblock = curpathpairs.Paths[0].mergeBlock.BB;

                        //This condition will never triggered
                        //Otherwise there is an error 
                        if(!succblock)
                            OP<<"Err: No succblock "<<"\n";
                        
                        TI = succblock->getTerminator();
                        NumSucc = TI->getNumSuccessors();

                        goto Branch_Check; 
                    }
                }

                //No path is recovered, which means the path info is the same
                if(!recovertag){
                    
                    //OP << "No path is recovered\n";
                    PathPairs nextpathpair;
                    nextpathpair.startBlock = curpathpairs.Paths[0].startBlock;

                    //Find the top block
                    set<BasicBlock *> unrecoveredblockset;
                    unrecoveredblockset.clear();
                    for(auto i = recoverset.begin(); i != recoverset.end();i++){
                        unrecoveredblockset.insert(i->first);
                        //OP << "block: "<<getBlockName(i->first)<<"\n";
                    }
                    BasicBlock * topblock = findTopBlock(unrecoveredblockset, connectGraph);

                    //These paths does not merge at all
                    //But this is not the case that all blocks are return blocks, just different merge blocks
                    if(topblock == NULL){

                        #ifdef DEBUG_PATH_COLLECTION_RESULT
                        OP <<"Unbranched paths!\n";
                        #endif

                        //Find another non-return top block (there must be at least one such block)
                        for(auto i = recoverset.begin(); i != recoverset.end();i++){
                            if(!checkReturnBlock(i->first,edgeIgnoreMap)){
                                topblock = i->first;
                                break;
                            }
                        }

                    }

                    #ifdef DEBUG_PATH_COLLECTION_RESULT
                    OP << "Top block: block-" <<getBlockName(topblock) << "\n";
                    #endif

                    //First finish the collection of current branch
                    for(auto i = recoverset.begin(); i != recoverset.end();i++){
                        
                        if(i->first != topblock){
                            nextpathpair.Paths.push_back(curpathpairs.Paths[*i->second.begin()]);
                            nextpathpair.mergeBlocks.insert(curpathpairs.Paths[*i->second.begin()].mergeBlock);
                            continue;
                        }

                        int indegree = indegreeMap[i->first];
                        indegreeMap[i->first] = 1;

                        SinglePath Path;
                        //Note: Path does not start from i->first!
                        Path.startBlock = curpathpairs.Paths[0].startBlock;
                        BasicBlock * nextsuccblock;

                        int index = *(i->second.begin());
                        Path.CBChain.insert(Path.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());
                        Path.CBChain.pop_back();
                        nextsuccblock = curpathpairs.Paths[index].mergeBlock.BB;
                        //OP << "nextsuccblock: "<<getBlockName(nextsuccblock)<<"\n";

                        //Then determin the return path
                        if(returnpath.getPathLength()==0 && !checkReturnBlock(i->first,edgeIgnoreMap)){
                            returnpath.CBChain.insert(returnpath.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());
                            
                            #ifdef DEBUG_PATH_COLLECTION_RESULT                          
                            OP << "returnpath added: ";
                            printSinglePath(returnpath);
                            #endif
                        }

                        //The path start from i->first is traveled before
                        if(branchvisitMap.count(i->first) == 1){
                            //OP <<"Here\n";
                            auto Path_Map = branchvisitMap[i->first];
                            Path.CBChain.insert(Path.CBChain.end(),Path_Map.CBChain.begin(),Path_Map.CBChain.end());
                            Path.mergeBlock = Path.CBChain.back();
                        }
                        else{
                            recurFindPaths(branchvisitMap, edgeIgnoreMap,indegreeMap,nextsuccblock,connectGraph,Path,PathGroup);
                        }

                        //Finish path collection once find a merge block
                        nextpathpair.Paths.push_back(Path);
                        nextpathpair.mergeBlocks.insert(Path.mergeBlock);
                        
                        //Update branchvisitMap
                        if(branchvisitMap.count(i->first) == 0){

                            SinglePath tmpPath;
                            int curpathlength = curpathpairs.Paths[index].getPathLength();
                            for(int i = curpathlength-1; i<Path.getPathLength(); i++){
                                tmpPath.CBChain.push_back(Path.CBChain[i]);
                            }

                            branchvisitMap[i->first] = tmpPath;
                            
                            #ifdef DEBUG_PATH_COLLECTION_RESULT
                            OP << "++BranchvisitMap updated, start from: "<< getBlockName(i->first) <<"\n";
                            OP << "++Added path: ";
                            printSinglePath(tmpPath);
                            #endif
                        }

                        Path.CBChain.clear();

                        indegreeMap[i->first] = indegree;
                        
                    }

                    //Then determin the return path

                    curpathpairs.startBlock = nextpathpair.startBlock;
                    curpathpairs.Paths.clear();
                    curpathpairs.Paths.assign(nextpathpair.Paths.begin(),nextpathpair.Paths.end());
                    curpathpairs.mergeBlocks.clear();
                    curpathpairs.mergeBlocks.insert(nextpathpair.mergeBlocks.begin(),nextpathpair.mergeBlocks.end());
                    goto MergeCheck;
                }

                /////////////////////////////////////////////////////////////////////
                //The we choose one path from all different path pairs in recoverset
                /////////////////////////////////////////////////////////////////////

                //Path recovery successfully
                PathPairs nextpathpair;
                nextpathpair.startBlock = curpathpairs.Paths[0].startBlock;

                for(auto i = recoverset.begin(); i != recoverset.end();i++){

                    SinglePath Path;
                    Path.startBlock = curpathpairs.Paths[0].startBlock;

                    BasicBlock * nextsuccblock;

                    if(i->second.size()==1){
                        int index = *(i->second.begin());
                        Path.CBChain.insert(Path.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());
                        nextsuccblock = curpathpairs.Paths[index].mergeBlock.BB;

                    }
                    else{
                        //Find a shortest path as the chosen path in next round
                        int index = -1;
                        int minlength = 100000;
                        for(auto it = i->second.begin(); it!=i->second.end();it++){
                            int curlength = curpathpairs.Paths[*it].getPathLength();
                            if(minlength > curlength){
                                minlength = curlength;
                                index = *it;
                            }
                        }

                        Path.CBChain.insert(Path.CBChain.end(),curpathpairs.Paths[index].CBChain.begin(),curpathpairs.Paths[index].CBChain.end());
                        nextsuccblock = curpathpairs.Paths[index].mergeBlock.BB;
                    }

                    Path.mergeBlock = Path.CBChain.back();
                
                    //Finish path collection once find a merge block
                    nextpathpair.Paths.push_back(Path);
                    nextpathpair.mergeBlocks.insert(Path.mergeBlock);

                    Path.CBChain.clear();
                }

                curpathpairs.startBlock = nextpathpair.startBlock;
                curpathpairs.Paths.clear();
                curpathpairs.Paths.assign(nextpathpair.Paths.begin(),nextpathpair.Paths.end());
                curpathpairs.mergeBlocks.clear();
                curpathpairs.mergeBlocks.insert(nextpathpair.mergeBlocks.begin(),nextpathpair.mergeBlocks.end());
                goto MergeCheck;
            }
        }
    }
}