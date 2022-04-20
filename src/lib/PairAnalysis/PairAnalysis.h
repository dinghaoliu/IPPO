#ifndef _PAIR_ANALYSIS_H
#define _PAIR_ANALYSIS_H

#include <llvm/Analysis/BasicAliasAnalysis.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <queue>
#include "../Analyzer.h"
#include "../Tools.h"
#include <fstream>

#define USE_RECURSION 0

//Path pairs collection and comparition
class PairAnalysisPass : public IterativeModulePass {

    //Define compound basic block structure
    typedef struct CompoundBlock {
        llvm::BasicBlock *BB;
        std::vector <llvm::Function *> CallFunctionSet;
        bool ignore;
        bool branch;
        bool merge;
        int trueprednum;
        //Todo: Add other features and tags

        CompoundBlock(){
            BB = NULL;
            CallFunctionSet.clear();
            ignore = false;
            branch = false;
            merge = false;
            trueprednum = -1;
        }

        friend bool operator< (const CompoundBlock& CB1, const CompoundBlock& CB2){
            return (CB1.BB < CB2.BB);
        }

    } CompoundBlock;

    //Define a single path in a function
    typedef struct SinglePath {
        std::vector<CompoundBlock> CBChain;
        llvm::Value *enterValue;
        llvm::Value *returnValue;
        CompoundBlock startBlock;
        CompoundBlock mergeBlock;
        bool isNormalPath;                  //If this path is a normal path or an error path
        //Todo: Add other features

        SinglePath(){
            CBChain.clear();
            returnValue = NULL;
            enterValue = NULL;
            isNormalPath = true;
        }

        SinglePath(std::vector<CompoundBlock> Chain){
            CBChain.assign(Chain.begin(),Chain.end());
        }

        int getPathLength(){
            return CBChain.size();
        }

        int getInstNumber(){
            int num = 0;
            for(int i = 0; i < CBChain.size();i++){
                CompoundBlock CB = CBChain[i];
                BasicBlock* BB = CB.BB;
                for(BasicBlock::iterator I = BB->begin(), IE = BB->end();
                    I != IE; ++I) {
                    num++;
                }
            }
            return num;
        }

        BasicBlock * getEndBlock(){
            if(CBChain.empty())
                return NULL;
            else{
                return CBChain.back().BB;
            }
        }

        bool checkBlockInPath(BasicBlock *bb){
            if(bb == NULL)
                return false;
            for(int i = 0; i < CBChain.size();i++){
                CompoundBlock CB = CBChain[i];
                BasicBlock* BB = CB.BB;
                if(BB == bb)
                    return true;
            }
            return false;
        }

    } SinglePath;

    //Define path pairs in a function
    //Path pairs in PathPairs share the same startBlock but could have diverse endings 
    //Path pairs in PathPairs make up the basic comparition unit
    //A function could have multiple PathPairs 
    typedef struct PathPairs {
        std::vector<SinglePath> Paths;
        CompoundBlock startBlock;               //branch or switch block
        std::set<CompoundBlock> mergeBlocks;    //merge blocks
        //Todo: Add other features

        PathPairs(){
            Paths.clear();
            mergeBlocks.clear();
        }

        PathPairs(std::vector<SinglePath> Allpath){
            Paths.assign(Allpath.begin(),Allpath.end());
        }

        int getPathNum(){
            return Paths.size();
        }

        bool UpdatedMergeSet(){
            if(Paths.empty())
                return true;

            //Paths is not empty
            for(int i=0;i<Paths.size();i++){
                if(!Paths[i].mergeBlock.BB){
                    OP<<"Wrong when update mergeset, start at"<< getBlockName(startBlock.BB) <<"\n";
                    return false;
                }
                CompoundBlock b = Paths[i].mergeBlock;
                mergeBlocks.insert(b);
            }
            return true;
        }

    } PathPairs;

    typedef struct CriticalVar{
        Value* inst; //The checked var
        Value* check;//critical var is used in this check inst
                     //Usually this is a br/switch/call inst
                     //And usually this is the pred inst of var
        //unsigned LineNo;
        int SOType;

        bool source_from_outside;
        bool source_from_funccall;

        //Value* source; //Also inst
        std::set<Value *> sourceset;
        std::map<Value *,std::vector<Value *>> getelementptrInfo;
        std::set<string>sourcefuncs;

        //Used in resource release check
        Value* resource_acq_inst;
        Value* resource_release_inst;
        
        int securityoperationtype;

        CriticalVar(){
            check = NULL;
            inst = NULL;
            SOType = -1;
            source_from_outside = false;
            source_from_funccall = false;
            //LineNo = -1;
            //source = NULL;
            sourceset.clear();
            getelementptrInfo.clear();
            sourcefuncs.clear();

            resource_acq_inst = NULL;
            resource_release_inst = NULL;
        }

        friend bool operator< (const CriticalVar& CV1, const CriticalVar& CV2){
            return (CV1.inst < CV2.inst);
        }

    } CriticalVar;
 

    typedef std::map<BasicBlock *,int> BBIndegreeMap;
    //typedef std::map<BasicBlock *,bool> BranchIgnoreMap;

    typedef std::pair<Instruction *, BasicBlock *> CFGEdge;
    typedef std::pair<CFGEdge, Value *> EdgeValue;

    //<1:ignore  >=1: not ignore
    //Use int rather than bool, int is used to record 
    //block num in path in recurMarkComplexIfEdgeMap
    typedef std::map<CFGEdge, int> EdgeIgnoreMap;
    
    typedef std::pair<BasicBlock*, BasicBlock*> Blockpair;
    typedef std::map<Blockpair, bool> ConnectGraph;

    //Return value check:
    enum ErrFlag {
		// error returning, mask:0xF
		Must_Return_Err = 1,
		May_Return_Err = 2,
		Not_Return_Err = 0,
		Reserved_Return2 = 8,
		// error handling, mask: 0xF0
		Must_Handle_Err = 16,
		May_Handle_Err = 32,
		Reserved_Handle1 = 64,
		Reserved_Handle2 = 128,
		Completed_Flag = 256,
	};
    typedef std::map<BasicBlock *, int> BBErrMap;
    static set<Instruction *>ErrSelectInstSet;
    typedef std::map<CFGEdge, int> EdgeErrMap;

    private:
    
        ////////////////////////////////////////////////////////
        //Path pair collection
        ////////////////////////////////////////////////////////

        bool updateConnectGraph(ConnectGraph &connectGraph, 
            std::vector<BasicBlock*> globalblockset);

        void initConnectGraph(Function *F,ConnectGraph &connectGraph,
            std::vector<BasicBlock*> globalblockset,
            EdgeIgnoreMap edgeIgnoreMap);
        
        bool checkBlockAToB_Version2(BasicBlock*a, BasicBlock *b,
            ConnectGraph connectGraph);

        //Check if a basic block is a branch block with the help of edgeIgnoreMap
        bool checkBranchWithMap(BasicBlock *bb, 
            EdgeIgnoreMap edgeIgnoreMap);

        //Check if a basic block is a merge block with the help of edgeIgnoreMap
        bool checkMergeWithMap(BasicBlock *bb, 
            EdgeIgnoreMap edgeIgnoreMap);

        void initIndegreeMap(Function *F, 
            std::map<BasicBlock*, int> &indegreeMap,
            EdgeIgnoreMap edgeIgnoreMap);

        void initNormalEdgeMap(Function *F,
            EdgeIgnoreMap &normalEdgeMap,
            EdgeIgnoreMap errEdgeMap
        );

        void addSelfLoopEdges(Function *F,
            EdgeIgnoreMap &edgeIgnoreMap
        );

        //Recursively find paths
        void recurFindPaths(std::map<BasicBlock *,SinglePath> &branchvisitMap,
            EdgeIgnoreMap &edgeIgnoreMap,
            std::map<BasicBlock*, int> &indegreeMap,
            BasicBlock *bb, 
            ConnectGraph &connectGraph,
            SinglePath &curpath,
            //std::vector<SinglePath> &Paths, 
            std::vector<PathPairs> &PathGroup);
        
        void initGlobalPathMap(std::vector<PathPairs> PathGroup,
            std::map<BasicBlock *, PathPairs> &GlobalPathMap);

        void initPairFuncCallSet(set<Value *> pathvalueset,
            set<Value *> &pairfunccallset,
            set<Value *> GlobalPairFuncSet);
        
        void initRefcountFuncCallSet(set<Value *> pathvalueset,
            set<Value *> &refcountfunccallset,
            set<Value *> GlobalRefCountFuncSet);

        void initUnlockFuncCallSet(set<Value *> pathvalueset,
            set<Value *> &lockfunccallset,
            set<Value *> &unlockfunccallset,
            set<Value *> GlobalLockFuncSet,
            set<Value *> GlobalUnlockFuncSet);

        void initGlobalPairFuncSet(Function *F, 
            set<Value *> &GlobalPairFuncSet);

        void initGlobalRefcountFuncSet(Function *F,
            set<Value *> &GlobalUnlockFuncSet);

        void initGlobalUnlockFuncSet(Function *F,
            set<Value *> &GlobalLockFuncSet,
            set<Value *> &GlobalRefCountFuncSet);
        
        void initEdgeIgnoreMap_Init(Function *F, 
            map<Value*,EdgeIgnoreMap> &edgeIgnoreMap_init);


        ////////////////////////////////////////////////////////
        //Return value check
        ////////////////////////////////////////////////////////
        
        // Find and record blocks with error returning
	    void checkErrReturn(Function *F, BBErrMap &bbErrMap,
            std::map<BasicBlock *,Value *> &blockAttributeMap);

        // Find and record blocks with error handling 
	    void checkErrHandle(Function *F, BBErrMap &bbErrMap);

        // Collect all blocks that influence the return value
	    void checkErrValueFlow(Function *F, ReturnInst *RI, 
			std::set<Value *> &PV, BBErrMap &bbErrMap,
            std::map<BasicBlock *,Value *> &blockAttributeMap);
        

        bool isValueErrno(Value *V, Function *F);

        // Mark the given block with an error flag.
	    void markBBErr(BasicBlock *BB, ErrFlag flag, BBErrMap &bbErrMap);

        // A lighweiht and inprecise way to check if the function may
	    // return an error
	    bool mayReturnErr(Function *F);
        
        // infer error-handling branch for a condition
	    int inferErrBranch(Instruction *Cond);

        // Find same-origin variables from the given variable
	    void findSameVariablesFrom(Value *V, std::set<Value *> &VSet);

        // Traverse CFG to mark all edges with error flags
	    bool markAllEdgesErrFlag(Function *F, BBErrMap &bbErrMap, EdgeErrMap &edgeErrMap);

        // Some return values of function cannot be identified, use this to solve this problem
        void markCallCases(Function *F,Value * Cond, EdgeErrMap &edgeErrMap);

        // Recursively mark edges from the error-handling block to the
        // closest branches
        void recurMarkEdgesToErrHandle(BasicBlock *BB, EdgeErrMap &edgeErrMap);

        // Incorporate newFlag into existing flag
        void updateReturnFlag(int &errFlag, int &newFlag);
        void updateHandleFlag(int &errFlag, int &newFlag);
        void mergeFlag(int &errFlag, int &newFlag);

        // Recursively mark all edges to the given block
        void recurMarkEdgesToBlock(CFGEdge &CE, int flag, 
                BBErrMap &bbErrMap, EdgeErrMap &edgeErrMap);

        // Recursively mark all edges from the given block
        void recurMarkEdgesFromBlock(CFGEdge &CE, int flag, 
                BBErrMap &bbErrMap, EdgeErrMap &edgeErrMap);

        // Recursively mark edges to the error-returning block
	    void recurMarkEdgesToErrReturn(BasicBlock *BB, int flag, EdgeErrMap &edgeErrMap);

        // Dump marked edges.
	    void dumpErrEdges(EdgeErrMap &edgeErrMap);
        
        bool checkEdgeErr(CFGEdge edge, EdgeErrMap edgeErrMap);

        ////////////////////////////////////////////////////////
        //Differential Check
        ////////////////////////////////////////////////////////

        //Execute security check analysis against path pairs in PathGroup
        void similarPathAnalysis(Function *F,
            std::vector<PathPairs> &PathGroup,
            ConnectGraph connectGraph,
            map<Value*,EdgeIgnoreMap> edgeIgnoreMap_init,
            EdgeIgnoreMap edgeIgnoreMap,
            bool in_err_paths);

        void similarPathAnalysis_singlePathpair(Function *F,
            PathPairs pathpairs,
            ConnectGraph connectGraph,
            map<Value*,EdgeIgnoreMap> edgeIgnoreMap_init,
            EdgeIgnoreMap edgeIgnoreMap,
            bool in_err_paths);

        //Used in similarPathAnalysis_singlePathpair
        void differentialCheck_SecurityCheck(Function *F,
            PathPairs pathpairs,
            int i, int j,
            std::vector<set<Value *>>pathvalueset_vector,
            std::map<int, set<CriticalVar>> pathpaircriticalarr,
            std::map<int, set<CriticalVar>> pathpairnormalarr,
            set<string> &reportSet);
        
        void differentialCheck_Refcount(Function *F,
            PathPairs pathpairs,
            int i, int j,
            map<int, set<Value *>> pathpairfuncpairarr,
            set<string> &reportSet);

        void differentialCheck_Unlock(Function *F,
            PathPairs pathpairs,
            int i, int j,
            map<int, set<Value *>> pathpairlockarr,
            map<int, set<Value *>> pathpairunlockarr,
            set<string> &reportSet);
        
        void differentialCheck_ResourceRelease(Function *F,
            PathPairs pathpairs,
            int i, int j,
            map<int, set<CriticalVar>> resourcereleasefuncpairarr,
            std::map<int, set<CriticalVar>> pathpairnormalarr,
            EdgeIgnoreMap edgeIgnoreMap,
            set<string> &reportSet);
        

        bool findCommonPairFunc(set<Value *> VS, Value* CV, BasicBlock* CommonHead);
        bool findCommonRefcountFunc(set<Value *> VS, Value* CV);
        bool findCommonUnlockFunc(set<Value *> VS, Value* CV);

        bool checkCondofCommonHead(Function *F, BasicBlock* CommonHead);
        bool checkTargetinCommonHeadCond(Value *targetvar, BasicBlock* CommonHead);

        bool checkPreReleaseBranch(Function *F, 
            BasicBlock* CommonHead, 
            Value* releaseoperation,
            EdgeIgnoreMap edgeIgnoreMap);

        bool checkDirectReturn(SinglePath path, Value* normalinst);
        void initPostConditions(SinglePath path, 
            Value* target_V, stack<Value *> &post_condistions);
        
        //Return true if this is the target catch case
        bool checkFuncFailinIf(Value* funccall, SinglePath path);

        //Todo: Compare exsiting states of path pairs (similar or not)

        
        ////////////////////////////////////////////////////////
        //Missing Resource Release Crosscheck related
        ////////////////////////////////////////////////////////
        bool checkValueEscape(Function *F, 
            Value *cirticalvalue,
            set<Value *>pathvalueset);
        
        bool checkValueRedefine(Function *F,
            Value *cirticalvalue,
            BasicBlock *CommonHead,
            EdgeIgnoreMap edgeIgnoreMap);

        ////////////////////////////////////////////////////////
        //Test functions
        ////////////////////////////////////////////////////////

        //Initialize pathvalueset (function)
        void initPathValueSet(Function *F,
            std::set<Value *> &pathvalueset);
        
        //Initialize pathvalueset (singlepath)
        void initPathValueSet(SinglePath singlepath,
            std::set<Value *> &pathvalueset);

        //This function comes from SecurityCheck.cc
        void findSameVariablesFrom(Function *F,
            CriticalVar &criticalvar,
            std::set<CFGEdge>pathedgeset
            //Value *V, 
            //set<Value*> &VSourceSet,
            //std::set<Value *>pathvalueset
            );
        
        //Find if two criticalvars share the same source
        bool findCVSource(CriticalVar CVA, CriticalVar CVB);

        //Return true if this value is checked
        bool checkUseChain(Value *V, SinglePath path);
        
        //Find the top block
        BasicBlock * findTopBlock(std::set<BasicBlock *> blockset, ConnectGraph connectGraph);
        BasicBlock * findTopBlock(std::set<BasicBlock *> blockset);
        BasicBlock * findBottomBlock(std::set<BasicBlock *> blockset);


        //Check if there is a path from fromBB to toBB 
        bool checkBlockPairConnectivity(
            BasicBlock* fromBB, 
            BasicBlock* toBB,
            EdgeIgnoreMap edgeIgnoreMap);
        
        bool checkBlockPairConnectivity(BasicBlock* fromBB, BasicBlock* toBB);

        //Get the condition of a branch inst
        LoadInst *getBranchCondition(Instruction *TI);
                
        ////////////////////////////////////////////////////////
        //Debug functions
        ////////////////////////////////////////////////////////

        void showEdgeIgnoreMap(EdgeIgnoreMap edgeIgnoreMap);
        void printSinglePath(SinglePath singlepath);
        unsigned getBranchLineNo(SinglePath singlepath);
        bool checkReturnBlock(BasicBlock *bb, EdgeIgnoreMap edgeIgnoreMap);

    public:
        PairAnalysisPass(GlobalContext *Ctx_)
         : IterativeModulePass(Ctx_, "PairAnalysis") { }
        virtual bool doInitialization(llvm::Module *);
        virtual bool doFinalization(llvm::Module *);
        virtual bool doModulePass(llvm::Module *);
        
        virtual void run(ModuleList &modules);

};


#endif