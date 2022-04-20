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

#include "PairAnalysis.h"
using namespace llvm;

//#define SINGLE_FUNCTION_DEBUG_PRINT 1
//#define PRINT_PATH_PAIR_RESULT
//#define TEST_ONE_CASE "target_function_name"
//#define PRINT_FUNCTION_NAME
//#define DUMP_ERR_EDGE
//#define CONCURRENT
#define MAX_BLOCK_NUM 500

bool PairAnalysisPass::doInitialization(Module *M) {
    return false;
}

bool PairAnalysisPass::doFinalization(Module *M) {
    return false;
}

void PairAnalysisPass::run(ModuleList &modules) {

	ModuleList::iterator i, e;
	OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
	bool again = true;

	//Initialize
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			again |= doInitialization(i->first);
			OP << ".";
		}
	}
	OP << "\n";

	//Execute main analysis pass
	unsigned iter = 0, changed = 1;
	while (changed) {
		++iter;
		changed = 0;
		unsigned counter_modules = 0;
		unsigned total_modules = modules.size();

#ifdef CONCURRENT
		#pragma omp parallel for
#endif
        for (int it = 0; it < total_modules; ++it) {
			OP << "[" << ID << " / " << iter << "] ";
			OP << "[" << ++counter_modules << " / " << total_modules << "] ";
			OP << "[" << modules[it].second << "]\n";

			bool ret = doModulePass(modules[it].first);
			if (ret) {
				++changed;
				OP << "\t [CHANGED]\n";
			} else
				OP << "\n";
		}
		OP << "[" << ID << "] Updated in " << changed << " modules.\n";
	}

	//Postprocessing
	OP << "[" << ID << "] Postprocessing ...\n";
	again = true;
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			// TODO: Dump the results.
			again |= doFinalization(i->first);
		}
	}

	OP << "[" << ID << "] Done!\n\n";
}

//Main function
bool PairAnalysisPass::doModulePass(Module *M) {

    ofstream in;
    
    for(Module::iterator f = M->begin(), fe = M->end();	f != fe; ++f){
        Function *F = &*f;

        if(F->empty())
            continue;
        
        //Skip functions in skipfunc list
        if(1 == Ctx->SkipFuncs.count(F->getName())){
            continue;
        }
            
        //F is not empty or ignored
        Ctx->NumFunctions++;

#ifdef TEST_ONE_CASE
        //Only test specific function
        if(F->getName()!= TEST_ONE_CASE){
            continue;
        }
#endif
        
        if(1 == Ctx->Loopfuncs.count(F)){
            continue;
        }

        /*if(Ctx->SecurityOperationSets.count(F) == 0){
            continue;
        }*/

#ifdef PRINT_FUNCTION_NAME
        OP << "Current func: " << F->getName() << "\n";
#endif
        
        //Get the first basic block
        Function::iterator bb = F->begin();
        BasicBlock * B = &*bb;

        //Print all blocks and their line number
#ifdef SINGLE_FUNCTION_DEBUG_PRINT
        
        for(Function::iterator b = F->begin(); 
            b != F->end(); b++){
            BasicBlock * bb = &*b;
            OP << "Block-"<<getBlockName(bb)<<" ";
            printBlockMessage(bb);
        }
#endif  

        vector<BasicBlock*> globalblockset;
        initGlobalBlockSet(F,globalblockset);

        //If the block number is too large, then we ignore this function
        if(globalblockset.size()>MAX_BLOCK_NUM){
            Ctx->Longfuncs.insert(F);
            globalblockset.clear();
            OP << "Long func: "<< F->getName()<<"\n";
            continue;
        }

        //Record the return value of May_Return_Err block
        map<BasicBlock *,Value *> blockAttributeMap;
        blockAttributeMap.clear();

        //Return value check
        BBErrMap bbErrMap;
        set<BasicBlock *> normalblockSet;
        bbErrMap.clear(), normalblockSet.clear();
        EdgeErrMap edgeErrMap;
        edgeErrMap.clear();
        
        // Find and record basic blocks that set error returning code
        checkErrReturn(F, bbErrMap, blockAttributeMap);
        for(auto i = bbErrMap.begin(); i != bbErrMap.end();i++){
            BasicBlock* bb = i->first;
            int CV = i->second;

            if(CV == Not_Return_Err){
                bbErrMap[bb] = May_Return_Err;
                normalblockSet.insert(bb);
            }
        }

        // Find and record basic blocks that have error handling code
        Type* return_value_type = F->getReturnType();
        if(return_value_type->isVoidTy()){
            checkErrHandle(F, bbErrMap);
        }
        //checkErrHandle(F, bbErrMap);

        markAllEdgesErrFlag(F, bbErrMap, edgeErrMap);
        
        for(auto it = blockAttributeMap.begin(); it != blockAttributeMap.end();it++){
            markCallCases(F, it->second, edgeErrMap);
        }

#ifdef DUMP_ERR_EDGE
        dumpErrEdges(edgeErrMap);
#endif    
        
        // Find all error edges in CFG
        EdgeIgnoreMap errEdgeMap;
        errEdgeMap.clear();
        for(auto it = edgeErrMap.begin(); it != edgeErrMap.end();it++){
            CFGEdge edge = it->first;
		    int flag = it->second;

            //Found an error edge
            if(!checkEdgeErr(edge,edgeErrMap)){
                pair<CFGEdge,int> value(edge,1);
                errEdgeMap.insert(value);
            }
        }

        //dumpErrEdges(errEdgeMap);

        /////////////////////////////////////////////////////////////////////
        //************************
        //*Recursively find paths*
        //************************
        /////////////////////////////////////////////////////////////////////
        std::vector<PathPairs> PathGroup;
        PathGroup.clear();
        std::vector<PathPairs> PathGroup_Normal;
        PathGroup_Normal.clear();
        std::vector<PathPairs> PathGroup_Error;
        PathGroup_Error.clear();

        map<BasicBlock *,SinglePath> branchvisitMap;
        branchvisitMap.clear();

        //Prepair this for missing init detection
        //Generate a edgeIgnoremap that ignore init operations
        map<Value*,EdgeIgnoreMap> edgeIgnoreMap_init;
        //Todo: design a better filter strategy
        //initEdgeIgnoreMap_Init(F, edgeIgnoreMap_init);

        /////////////////////////////////////////////////////////////////////
        //----------First we ignore the error edges and only collect normal path pairs
        /////////////////////////////////////////////////////////////////////
        SinglePath curpath;
        curpath.CBChain.clear();

        EdgeIgnoreMap edgeIgnoreMap_normal;
        edgeIgnoreMap_normal = errEdgeMap;
        addSelfLoopEdges(F,edgeIgnoreMap_normal); //also ignore loop edge

        map<BasicBlock*,int> indegreeMap;
        initIndegreeMap(F,indegreeMap,edgeIgnoreMap_normal);
        
        //dumpErrEdges(edgeIgnoreMap_normal);
        
        ConnectGraph connectGraph;
        initConnectGraph(F,connectGraph, globalblockset, edgeIgnoreMap_normal);

        //Collect normal path pairs
        recurFindPaths(branchvisitMap,edgeIgnoreMap_normal,indegreeMap,B,connectGraph,curpath,PathGroup_Normal);
        similarPathAnalysis(F,PathGroup_Normal,connectGraph,edgeIgnoreMap_init,edgeIgnoreMap_normal,false);


        /////////////////////////////////////////////////////////////////////
        //-----------Then we target the error paths
        /////////////////////////////////////////////////////////////////////
        SinglePath curpath2;
        curpath2.CBChain.clear();
        B = &*bb;

        EdgeIgnoreMap normalEdgeMap;
        initNormalEdgeMap(F,normalEdgeMap,errEdgeMap);
        //showEdgeIgnoreMap(normalEdgeMap);
    
        //dumpErrEdges(normalEdgeMap);
        
        branchvisitMap.clear();
        EdgeIgnoreMap edgeIgnoreMap_bug = normalEdgeMap;
        addSelfLoopEdges(F,edgeIgnoreMap_bug);
        indegreeMap.clear();
        initIndegreeMap(F,indegreeMap,edgeIgnoreMap_bug);
        initConnectGraph(F,connectGraph, globalblockset, edgeIgnoreMap_bug);
        
        //Collect error path pairs
        recurFindPaths(branchvisitMap,edgeIgnoreMap_bug,indegreeMap,B,connectGraph,curpath2,PathGroup_Error);
        similarPathAnalysis(F,PathGroup_Error,connectGraph,edgeIgnoreMap_init,edgeIgnoreMap_bug,true);

        //Finally merge these two path pair groups
        PathGroup.insert(PathGroup.end(),PathGroup_Normal.begin(),PathGroup_Normal.end());
        PathGroup.insert(PathGroup.end(),PathGroup_Error.begin(),PathGroup_Error.end());
        

        //No path pairs are found
        if(PathGroup.empty()){
            continue;
        }

        //Print collected path pairs
#ifdef PRINT_PATH_PAIR_RESULT
        OP << "Current func: " << F->getName() << "\n"; 
        int n=0;
        int subn=0;

        for(int i=0;i<PathGroup.size();i++,n++){
            
            OP << "  Current path group: " << i+1 << "\n";
            PathPairs curpathpairs = PathGroup[i];
            
            BasicBlock *startbb = PathGroup[i].startBlock.BB;

            //Find every path pair
            for(int j=0;j<curpathpairs.getPathNum();j++){

                OP << "    Current single path: " << j+1 << "\n";
                SinglePath curpath = curpathpairs.Paths[j];
                OP << "      ";

                for(int k=0;k<curpath.getPathLength();k++){
                    BasicBlock* curbb = curpath.CBChain[k].BB;
                    OP << "Block-" << getBlockName(curbb) <<"  ";
                }
                OP << "\n";                
            }

            OP << "  Current path pairs end" <<"\n\n";
        }
#endif

        functionend:

        Ctx->NumPathPairs += PathGroup.size();

        //Clean
        curpath.CBChain.clear();
        PathGroup.clear();
        globalblockset.clear();
        connectGraph.clear();
        indegreeMap.clear();
        bbErrMap.clear();
        edgeErrMap.clear();
    }

    return false;
}
