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

//#define OP in

int GlobalBugNum = 0;


//Execute object based similar path analysis against path pairs in PathGroup
//There will be other checks in the future
void PairAnalysisPass::similarPathAnalysis(Function *F,
    std::vector<PathPairs> &PathGroup,
    ConnectGraph connectGraph,
    map<Value*,EdgeIgnoreMap> edgeIgnoreMap_init,
    EdgeIgnoreMap edgeIgnoreMap,
    bool in_err_paths){

    if(!F || PathGroup.empty())
        return;
    
    for(auto i = PathGroup.begin(); i != PathGroup.end(); i++){
        PathPairs curpathpair = *i;
        similarPathAnalysis_singlePathpair(F,curpathpair,connectGraph,edgeIgnoreMap_init,edgeIgnoreMap,in_err_paths);
    }
}

void PairAnalysisPass::initPairFuncCallSet(set<Value *> pathvalueset,
    set<Value *> &pairfunccallset,
    set<Value *> GlobalPairFuncSet){

    pairfunccallset.clear();
    
    if(pathvalueset.empty())
        return;
    
    for(auto it = pathvalueset.begin(); it != pathvalueset.end();it++){

        CallInst *CAI = dyn_cast<CallInst>(*it);
        if(CAI){
            if(1 == GlobalPairFuncSet.count(*it)){
                pairfunccallset.insert(*it);
            }
        }
    }
}

void PairAnalysisPass::initRefcountFuncCallSet(set<Value *> pathvalueset,
    set<Value *> &refcountfunccallset,
    set<Value *> GlobalRefCountFuncSet){
    
    refcountfunccallset.clear();

    if(pathvalueset.empty())
        return;
    
    for(auto it = pathvalueset.begin(); it != pathvalueset.end();it++){

        CallInst *CAI = dyn_cast<CallInst>(*it);
        if(CAI){
            if(1 == GlobalRefCountFuncSet.count(*it)){
                refcountfunccallset.insert(*it);
            }
        }
    }
}

void PairAnalysisPass::initUnlockFuncCallSet(set<Value *> pathvalueset,
    set<Value *> &lockfunccallset,
    set<Value *> &unlockfunccallset,
    set<Value *> GlobalLockFuncSet,
    set<Value *> GlobalUnlockFuncSet){
    
    unlockfunccallset.clear();

    if(pathvalueset.empty())
        return;
    
    for(auto it = pathvalueset.begin(); it != pathvalueset.end();it++){

        CallInst *CAI = dyn_cast<CallInst>(*it);
        if(CAI){

            if(1 == GlobalUnlockFuncSet.count(*it)){
                unlockfunccallset.insert(*it);
            }

            if(1 == GlobalLockFuncSet.count(*it)){
                lockfunccallset.insert(*it);
            }
        }
    }

}

void PairAnalysisPass::initGlobalPairFuncSet(Function *F, 
    set<Value *> &GlobalPairFuncSet){
    
    GlobalPairFuncSet.clear();
    
    if(!F)
        return;
    
    for(auto it = Ctx->SecurityOperationSets[F].begin(); it != Ctx->SecurityOperationSets[F].end();it++){

        SecurityOperation SO = *it;
        if(SO.operationType == PairFunc){
            GlobalPairFuncSet.insert(SO.branch);
        }
    }
}

void PairAnalysisPass::initGlobalRefcountFuncSet(Function *F,
    set<Value *> &GlobalRefCountFuncSet){
    
    GlobalRefCountFuncSet.clear();

    if(!F)
        return;
    
    for(auto it = Ctx->SecurityOperationSets[F].begin(); it != Ctx->SecurityOperationSets[F].end();it++){

        SecurityOperation SO = *it;
        if(SO.operationType == RefcountOperation){
            GlobalRefCountFuncSet.insert(SO.branch);
        }
    }
}

void PairAnalysisPass::initGlobalUnlockFuncSet(Function *F,
    set<Value *> &GlobalLockFuncSet,
    set<Value *> &GlobalUnlockFuncSet){

    GlobalUnlockFuncSet.clear();

    if(!F)
        return;
    
    for(auto it = Ctx->SecurityOperationSets[F].begin(); it != Ctx->SecurityOperationSets[F].end();it++){

        SecurityOperation SO = *it;
        if(SO.operationType == Unlock){
            GlobalUnlockFuncSet.insert(SO.branch);
        }

        if(SO.operationType == Lock){
            GlobalLockFuncSet.insert(SO.branch);
        }
    }
}


void PairAnalysisPass::initEdgeIgnoreMap_Init(Function *F, 
    map<Value*,EdgeIgnoreMap> &edgeIgnoreMap_init){

    edgeIgnoreMap_init.clear();

    if(!F)
        return;
    
    for(auto it = Ctx->SecurityOperationSets[F].begin(); it != Ctx->SecurityOperationSets[F].end();it++){
        
        SecurityOperation SO = *it;

        if(SO.operationType == Initialization){
            
            Value* initoperation = SO.branch; //init operation
            Value* initedvar = SO.checkedValue;

            auto Iinit = dyn_cast<Instruction>(initoperation);
            BasicBlock *init_operation_block = Iinit->getParent();
            Instruction *TI =init_operation_block->getTerminator();
            for(BasicBlock *Succ : successors(init_operation_block)){
                CFGEdge edge = make_pair(TI,Succ);
                pair<CFGEdge,int> value(edge,1);
                edgeIgnoreMap_init[initedvar].insert(value);
            }
        }
    }

    for(Function::iterator bb = F->begin(); bb != F->end(); bb++){
        for(BasicBlock::iterator i = bb->begin(); 
            i != bb->end(); i++){
            
            Instruction * inst = dyn_cast<Instruction>(i);
            CallInst *CAI = dyn_cast<CallInst>(i);
            if(CAI){
                
                StringRef FName = getCalledFuncName(CAI);
                if(FName != "llvm.dbg.declare")
                    continue;
                
                auto targetvar = CAI->getOperand(0);
                auto MD_targetvar = dyn_cast<MetadataAsValue>(targetvar);
                Metadata *M_targetvar = MD_targetvar->getMetadata();
                auto DIvartest = dyn_cast<ValueAsMetadata>(M_targetvar);
                if(DIvartest){

                    auto targetvar_v = DIvartest->getValue();

                    if(targetvar_v && edgeIgnoreMap_init.count(targetvar_v) != 0){

                        auto targetmetadata = CAI->getOperand(1);
                        //OP << "targetvar: "<<*targetvar <<"\n";
                        //OP << "targetmetadata: "<<*targetmetadata <<"\n";
                        auto MD = dyn_cast<MetadataAsValue>(targetmetadata);
                        Metadata *M = MD->getMetadata();
                        auto DIvar = dyn_cast<DIVariable>(M);
                        //OP << "name: "<< DIvar->getName() << "\n";
                        //OP << "line: "<< DIvar->getLine() << "\n";
                        auto varname = DIvar->getName();                        

                        //check use chain
                        for(User *U : targetvar_v->users()){
                            if(U == targetvar_v)
                                continue;
                            
                            BitCastInst *BCI = dyn_cast<BitCastInst>(U);
                            if(BCI){
                                for(User *U2 : BCI->users()){
                                    if(U2 == BCI)
                                        continue;
                                    U = U2;
                                }
                            }
                            
                            CallInst *CAI_in = dyn_cast<CallInst>(U);
                            if(CAI_in){
                                string CAI_sourcecode = getSourceLine(CAI_in);
                                //OP <<"CAI_sourcecode: "<<CAI_sourcecode<<"\n";
                                if(CAI_sourcecode.size() == 0)
                                    continue;

                                string targetstr = " &";
                                string targetstr2 = "(&";
                                string targetstr3 = "\t&";
                                targetstr.append(varname);
                                targetstr2.append(varname);
                                targetstr3.append(varname);
                                if(checkStringContainSubString(CAI_sourcecode,targetstr) ||
                                checkStringContainSubString(CAI_sourcecode,targetstr2) ||
                                checkStringContainSubString(CAI_sourcecode,targetstr3)){
                                    //OP<<"Found one: "<<targetstr<<"\n";
                                    BasicBlock* CAI_BB = CAI_in->getParent();
                                    Instruction *TI =CAI_BB->getTerminator();
                                    for(BasicBlock *Succ : successors(CAI_BB)){
                                        CFGEdge edge = make_pair(TI,Succ);
                                        pair<CFGEdge,int> value(edge,1);
                                        edgeIgnoreMap_init[targetvar_v].insert(value);
                                    }
                                }
                            }
                        }//end check use chain
                    }
                }
            }
        }
    }
}

//This function works on a path pair
void PairAnalysisPass::similarPathAnalysis_singlePathpair(Function *F, 
    PathPairs pathpairs, ConnectGraph connectGraph,
    map<Value*,EdgeIgnoreMap> edgeIgnoreMap_init,
    EdgeIgnoreMap edgeIgnoreMap,
    bool in_err_paths){

    if(pathpairs.getPathNum()==0)
        return;

    vector<map<Value *, int>> pathpaircheckarray;
    pathpaircheckarray.clear();

    map<int, set<CriticalVar>> pathpaircriticalarr;
    map<int, set<CriticalVar>> pathpairnormalarr;
    map<int, set<Value *>> pathpairfuncpairarr;
    map<int, set<Value *>> refcountfuncpairarr;
    map<int, set<Value *>> pathpairunlockarr;
    map<int, set<Value *>> pathpairlockarr;
    map<int, set<CriticalVar>> resourcereleasefuncpairarr;
    map<int, set<CriticalVar>> initoperationarr;
    pathpaircriticalarr.clear();
    pathpairnormalarr.clear();
    pathpairfuncpairarr.clear();
    refcountfuncpairarr.clear();
    pathpairunlockarr.clear();
    pathpairlockarr.clear();
    resourcereleasefuncpairarr.clear();
    initoperationarr.clear();

    vector<set<Value *>>pathvalueset_vector;
    pathvalueset_vector.clear();

    set<Value *> GlobalPairFuncSet;
    initGlobalPairFuncSet(F, GlobalPairFuncSet);
    set<Value *> GlobalRefCountFuncSet;
    initGlobalRefcountFuncSet(F, GlobalRefCountFuncSet);
    set<Value *> GlobalLockFuncSet;
    set<Value *> GlobalUnlockFuncSet;
    initGlobalUnlockFuncSet(F,GlobalLockFuncSet,GlobalUnlockFuncSet);

    //Travel all singlepaths in a pathpair
    //Check if security checks are in one path pair
    long int testnum = 0;
    for(auto i = pathpairs.Paths.begin(); i != pathpairs.Paths.end(); i++){
        SinglePath singlepath = *i;

        //Collect values in current singlepath
        set<Value *> pathvalueset;
        initPathValueSet(singlepath,pathvalueset);
        pathvalueset_vector.push_back(pathvalueset);

        set<CriticalVar> criticalvarset;
        set<CriticalVar> normalvarset;
        set<CriticalVar> resourcereleaseset;
        set<CriticalVar> initoperationset;
        criticalvarset.clear();
        normalvarset.clear();
        resourcereleaseset.clear();
        initoperationset.clear();

        set<Value *> pairfunccallset;
        initPairFuncCallSet(pathvalueset,pairfunccallset,GlobalPairFuncSet);
        set<Value *> refcountfunccallset;
        initRefcountFuncCallSet(pathvalueset,refcountfunccallset,GlobalRefCountFuncSet);
        set<Value *> unlockfunccallset;
        set<Value *> lockfunccallset;
        initUnlockFuncCallSet(pathvalueset,lockfunccallset,unlockfunccallset,GlobalLockFuncSet,GlobalUnlockFuncSet);

        set<Value *> refcountset;
        
        //map<Value *, int> checkedvaluemap;
        //checkedvaluemap.clear();
        set<CFGEdge> pathedgeSet;
        pathedgeSet.clear();
        for(auto j = singlepath.CBChain.begin(); j != singlepath.CBChain.end();j++){
            CompoundBlock CBB = *j;
            BasicBlock* BB = CBB.BB;

            if(BB == singlepath.getEndBlock())
                continue;

            auto TI = BB->getTerminator();
            BasicBlock* nextBB = (j+1)->BB;
            CFGEdge edge = make_pair(TI,nextBB);
            pathedgeSet.insert(edge);

        }

        for(auto j = singlepath.CBChain.begin(); j != singlepath.CBChain.end();j++){
            CompoundBlock CBB = *j;
            BasicBlock* BB = CBB.BB;

            //Collect all instructions of current path
            for(BasicBlock::iterator i = BB->begin(); i != BB->end(); i++){

                auto midinst = dyn_cast<Instruction>(i);

                CriticalVar CV;

                CV.resource_release_inst = &*i;
                CV.inst = &*i;

                //Find source of all values
                findSameVariablesFrom(F,CV,pathedgeSet);

                normalvarset.insert(CV);

                //Find security operations in current path
                for(auto i = Ctx->SecurityOperationSets[F].begin();i!=Ctx->SecurityOperationSets[F].end();i++){
                    SecurityOperation SO = *i;
                    Value* SOBranch = SO.branch; //first
                    Value* SOCheckedValue = SO.checkedValue; //second
                    int operationType = SO.operationType;

                    //auto I = dyn_cast<Instruction>(SOBranch);
                    //Find resource release
                    if(CV.resource_release_inst == SOBranch){

                        CV.SOType = operationType;

                        if(operationType == ResourceRelease){
                            //OP << "Found inside\n";
                            CV.inst = SOCheckedValue;
                            resourcereleaseset.insert(CV);
                        }
                    }

                    //Find initialization
                    if(operationType == Initialization){
                        if(CV.inst == SOBranch){
                            CV.SOType = operationType;
                            CV.check = SOCheckedValue; // The inited value
                            initoperationset.insert(CV);
                        }
                    }

                    if(operationType == Securitycheck){
                        if(CV.inst == SOBranch){
                            CV.SOType = operationType;
                            CV.check = SOCheckedValue; // The checked value
                            criticalvarset.insert(CV);
                        }
                    }

                }//End find security operation
            }
        }

        //Collect all values for each paths
        pair<int, set<CriticalVar>> cvalue(testnum,criticalvarset);
        pathpaircriticalarr.insert(cvalue);
        pair<int, set<CriticalVar>> nvalue(testnum,normalvarset);
        pathpairnormalarr.insert(nvalue);

        //Collect all pair functions for each paths
        pair<int, set<Value *>> pvalue(testnum,pairfunccallset);
        pathpairfuncpairarr.insert(pvalue);

        //Collect all refcount operations for each paths
        pair<int, set<Value *>> refcountvalue(testnum,refcountfunccallset);
        refcountfuncpairarr.insert(refcountvalue);

        //Collect all lock & unlock operations for each paths
        pair<int, set<Value *>> lockvalue(testnum,lockfunccallset);
        pathpairlockarr.insert(lockvalue);
        pair<int, set<Value *>> unlockvalue(testnum,unlockfunccallset);
        pathpairunlockarr.insert(unlockvalue);

        pair<int, set<CriticalVar>> rvalue(testnum,resourcereleaseset);
        resourcereleasefuncpairarr.insert(rvalue);

        pair<int, set<CriticalVar>> ivalue(testnum,initoperationset);
        initoperationarr.insert(ivalue);

        testnum++;
    }

    /* OP << "\n**********************\n";
    OP << "Begin to differential check\n";
    OP << "**********************\n"; */

    static set<string> reportSet;
    clock_t start_time, finish_time;
    //reportMap.clear();
    for(int i =0; i<pathpairs.getPathNum();i++){

        for(int j=i+1;j<pathpairs.getPathNum();j++){
            start_time = clock();
            //Differential  check missing check bugs
            differentialCheck_SecurityCheck(F,pathpairs,i,j,pathvalueset_vector,pathpaircriticalarr,pathpairnormalarr,reportSet);
            differentialCheck_SecurityCheck(F,pathpairs,j,i,pathvalueset_vector,pathpaircriticalarr,pathpairnormalarr,reportSet);
            finish_time = clock();
            Ctx->security_check_analysis += (double)(finish_time - start_time) / CLOCKS_PER_SEC;

            //Differential check refcount bugs
            differentialCheck_Refcount(F,pathpairs,i,j,refcountfuncpairarr,reportSet);
            differentialCheck_Refcount(F,pathpairs,j,i,refcountfuncpairarr,reportSet);

            //Differential check missing unlock bugs
            differentialCheck_Unlock(F,pathpairs,i,j,pathpairlockarr,pathpairunlockarr,reportSet);
            differentialCheck_Unlock(F,pathpairs,j,i,pathpairlockarr,pathpairunlockarr,reportSet);

            //if(!in_err_paths)
            //    continue;

            differentialCheck_ResourceRelease(F,pathpairs,i,j,resourcereleasefuncpairarr,pathpairnormalarr,edgeIgnoreMap,reportSet);
            differentialCheck_ResourceRelease(F,pathpairs,j,i,resourcereleasefuncpairarr,pathpairnormalarr,edgeIgnoreMap,reportSet);

        }
    }
}

//Consider use chain, check if CV shows in VS set
bool PairAnalysisPass::findCommonPairFunc(set<Value *> VS, Value* CV, BasicBlock* CommonHead){
    
    if(!CV || VS.empty())
        return false;
    
    CallInst *CAI_CV = dyn_cast<CallInst>(CV);
    StringRef CVFName = getCalledFuncName(CAI_CV);
    auto CV_Peerfunc_Name_set = Ctx->PairFuncs[CVFName];

    for(auto i = VS.begin(); i != VS.end(); i++){
        CallInst *CAI_VS = dyn_cast<CallInst>(*i);
        Function *CF_VS = CAI_VS->getCalledFunction();
        StringRef FName = getCalledFuncName(CAI_VS);
        
        if(FName == CVFName){
             
            //Check if CV in CommonHead
            if(CommonHead == NULL)
                return true;

            for(BasicBlock::iterator i = CommonHead->begin(); 
                i != CommonHead->end(); i++){

                auto midinst = dyn_cast<Instruction>(i);
                if(CV == midinst)
                    return false;
            }
            return true;
        }
        
        auto VS_Peerfunc_Name_set = Ctx->PairFuncs[FName];
        if(findCommonOfSet(VS_Peerfunc_Name_set,CV_Peerfunc_Name_set)){

            if(CommonHead == NULL)
                return true;
            
            for(BasicBlock::iterator i = CommonHead->begin(); 
                i != CommonHead->end(); i++){
                
                auto midinst = dyn_cast<Instruction>(i);
                if(CV == midinst)
                    return false;
            }
            
            return true;
        }            
    }

    //CV does not show in VS
    return false;
}

bool PairAnalysisPass::findCommonRefcountFunc(set<Value *> VS, Value* CV){
    if(!CV || VS.empty())
        return false;
    
    CallInst *CAI_CV = dyn_cast<CallInst>(CV);
    //Function *CF = CAI->getCalledFunction();
    StringRef CVFName = getCalledFuncName(CAI_CV);
    auto CV_Peerfunc_Name_set = Ctx->RefcountFuncs[CVFName];

    for(auto i = VS.begin(); i != VS.end(); i++){
        CallInst *CAI_VS = dyn_cast<CallInst>(*i);
        StringRef FName = getCalledFuncName(CAI_VS);

        if(FName == CVFName){
            return true;
        }

        auto VS_Peerfunc_Name_set = Ctx->RefcountFuncs[FName];
        if(findCommonOfSet(VS_Peerfunc_Name_set,CV_Peerfunc_Name_set)){
            return true;
        }
    }

    return false;
}

bool PairAnalysisPass::findCommonUnlockFunc(set<Value *> VS, Value* CV){
    if(!CV || VS.empty())
        return false;
    
    CallInst *CAI_CV = dyn_cast<CallInst>(CV);
    StringRef CVFName = getCalledFuncName(CAI_CV);

    for(auto i = VS.begin(); i != VS.end(); i++){
        CallInst *CAI_VS = dyn_cast<CallInst>(*i);
        StringRef FName = getCalledFuncName(CAI_VS);

        if(CAI_CV == CAI_VS)
            return true;
        
        if(CVFName == FName)
            return true;

    }

    return false;
}

//Check if the function pair only shows in path CV
//If both pair funcs are shown in only one path, then this is not a bug
//Return true if there is a real bug
bool checkPairFuncUse(string CV_Peerfunc_Name, set<Value *> CVPath, set<Value *> HeadValues){
    
    if(CV_Peerfunc_Name.size()==0 || CVPath.empty())
        return false;

    for(auto i = CVPath.begin(); i != CVPath.end(); i++){
        
        //In the head block, ignore it
        if(HeadValues.count(*i) == 1){
            continue;
        }

        CallInst *CAI = dyn_cast<CallInst>(*i);
        StringRef FName = getCalledFuncName(CAI);

        //Found both pear func use in CVPath
        if(FName == CV_Peerfunc_Name)
            return false;       
    }

    return true;
}

//Check if pair func appears in an if statement and fails
//Return true if this is the target catch case
bool PairAnalysisPass::checkFuncFailinIf(Value* funccall,
    SinglePath path){

    if(funccall == NULL || path.getPathLength()==0)
        return true;
    
    Instruction *funccall_I = dyn_cast<Instruction>(funccall);
    BasicBlock *callparentbb = funccall_I->getParent();
    Instruction *TI = callparentbb->getTerminator();

    //Not branch
    if (TI->getNumSuccessors() <= 1) {
        return false;
    }

    ///////////////////////////////////////////////
    //A simple solution
    ///////////////////////////////////////////////
    if(callparentbb == path.CBChain[0].BB){
        //OP<<"Stop here\n";
        //return true;
    }

    //Only consider branch inst
    Instruction *Cond = NULL;
    if (BranchInst *BI = dyn_cast<BranchInst>(TI))
        Cond = dyn_cast<Instruction>(BI->getCondition());
    if (!Cond)
        return false;
    
    set<BasicBlock *> pathblockset;
    pathblockset.clear();
    for(auto i = path.CBChain.begin(); i != path.CBChain.end();i++){
        BasicBlock * pathblock = i->BB;
        pathblockset.insert(pathblock);
    }

    //Check the use of funccall in current block
	for (User *U : funccall->users()) {
        if(U == funccall)
            continue;

        Instruction *I = dyn_cast<Instruction>(U);
        if(I->getParent() != callparentbb)
            continue;

        ICmpInst *ICI = dyn_cast<ICmpInst>(U);
        if(!ICI)
            continue;

        //A simple solution, just ignore pair functions in an if statements
        //return true;

        ICmpInst::Predicate Pred = ICI->getPredicate();
        auto oprand0 = I->getOperand(0);
        ConstantInt *CIBase = dyn_cast<ConstantInt>(ICI->getOperand(1));

        if (!CIBase)
		    return false;
        
        //return true;

        unsigned brID = -1;
        bool ptrType = oprand0->getType()->isPointerTy();
        switch (Pred) {
            case ICmpInst::ICMP_EQ:
                if (CIBase->isZero())
                    brID = 0;
            break;

            case ICmpInst::ICMP_NE:
                if (CIBase->isZero())
                    brID = 1;
            break;

            case ICmpInst::ICMP_SLT:
                if (CIBase->isZero())
                    brID = 0;
            break;

            default: break;
        }

        if(brID!=-1){
            BasicBlock * falsepathblock = TI->getSuccessor(brID);
            if(pathblockset.count(falsepathblock) == 1)
                return true;
        }
    }
    
    return false;
}


void PairAnalysisPass::differentialCheck_Unlock(Function *F,
    PathPairs pathpairs,
    int i, int j,
    map<int, set<Value *>> pathpairlockarr,
    map<int, set<Value *>> pathpairunlockarr,
    set<string> &reportSet){

    if(!F)
        return;
    
    if(pathpairs.getPathNum() == 0)
        return;
    
    if(pathpairunlockarr[i].empty() && pathpairunlockarr[j].empty())
        return;
    
    ofstream in;
    in.open("BugReports.txt",ios::app);

    //check if unlock in path j does not show in path i
    for(auto k=pathpairunlockarr[j].begin();k!=pathpairunlockarr[j].end();k++){
        
        Value * unlockcall= *k;
        CallInst *CV_CAI = dyn_cast<CallInst>(unlockcall);
        StringRef CV_FName = getCalledFuncName(CV_CAI);
        
        //unlock in path j does not show in path i
        if(!findCommonUnlockFunc(pathpairunlockarr[i],unlockcall)){

            bool findtag = false;

            //Check if a pair of lock&unlock only occur in path j
            set<Value *> HeadValues;
            HeadValues.clear();
            BasicBlock *CommonHead = pathpairs.Paths[j].CBChain[0].BB;

            for(BasicBlock::iterator i = CommonHead->begin(); i != CommonHead->end(); i++){
                HeadValues.insert(&*i);

            }
            for(auto it = pathpairlockarr[j].begin(); it != pathpairlockarr[j].end();it++){

                if(HeadValues.count(*it) == 1){

                    //Check pre-condition
                    if(checkFuncFailinIf(*it, pathpairs.Paths[j])){
                        findtag = true;
                        break;
                    }
                    else{
                        continue;
                    }
                }

                if(findtag == true)
                    break;
                    
                Value * lockcall= *it;
                CallInst *Lock_CAI = dyn_cast<CallInst>(lockcall);

                //Current critical var analysis is not precise, check source code to confirm
                //OP<<"LOCK_CAI: "<<*Lock_CAI<<"\n";
                string lock_sourcecode = getSourceLine(Lock_CAI);
                //OP<<"LOCK_CAI_source: "<<lock_sourcecode<<"\n";
                int start_lock = lock_sourcecode.find("(");
                if(start_lock<0)
                    continue;
                //OP<<"\n"<<start_lock<<"\n";
                string arg_lock = lock_sourcecode.substr(start_lock);
                string unlock_sourcecode = getSourceLine(CV_CAI);
                //OP<<"UNLOCK_CAI: "<<*CV_CAI<<"\n";
                //OP<<"UNLOCK_CAI_source: "<<unlock_sourcecode<<"\n";
                int start_unlock = unlock_sourcecode.find("(");
                if(start_unlock<0)
                    continue;
                //OP<<"\n"<<start_unlock<<"\n";
                string arg_unlock = unlock_sourcecode.substr(start_unlock);
                //OP<<"lockarg: "<<arg_lock<<"\n";
                //OP<<"unlockarg: "<<arg_unlock <<"\n";
                if(arg_lock == arg_unlock){
                    findtag = true;
                    break;
                }
            }

            if(findtag == true)
                continue;

            if(reportSet.count(F->getName()) == 1)
                continue;

            //Report a bug
            OP<<"\n=============================\n";
            printf("\033[31mWarning: find a potential bug:\033[0m\n");
            OP << "Global Bug num:" << GlobalBugNum++ <<"\n";
            string topfuncname = F->getName();
            OP << "File name: "<<getInstFilename(dyn_cast<Instruction>(unlockcall))<<"\n";
            
            OP << "Function: "<< topfuncname <<"\n";
            OP << "Bug Type: "<< "Missing unlock bug"<<"\n";
            OP << "-----------------------------\n";
            OP << "Current path pair start at block-"<<getBlockName(pathpairs.startBlock.BB)<<"\n";
            OP << "Refcount function is shown in path \'"<< j <<"\' but not in path \'"<<i<<"\'\n";
            OP << "--Path "<< j <<": ";
            //printSinglePath(pathpairs.Paths[j]);
            OP << " ";
            for(auto it = pathpairs.Paths[j].CBChain.begin(); it != pathpairs.Paths[j].CBChain.end();it++){
                CompoundBlock CBB = *it;
                BasicBlock* BB = CBB.BB;
                OP << "Block-"<<getBlockName(BB)<<" ";
            }
            OP << "\n";
            
            OP << "--Path "<< i <<": ";
            //printSinglePath(pathpairs.Paths[i]);
            OP << " ";
            for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
                CompoundBlock CBB = *it;
                BasicBlock* BB = CBB.BB;
                OP << "Block-"<<getBlockName(BB)<<" ";
            }
            OP << "\n";
            
            OP << "--Branch from line "<<getBranchLineNo(pathpairs.Paths[j])<<"\n";
            OP << "-----------------------------\n";
            OP << "Unlock Func("<<getInstLineNo(dyn_cast<Instruction>(unlockcall)) <<"): " << getValueContent(CV_CAI) <<"\n";
            OP<<"=============================\n";
            Ctx->NumBugs++;
            reportSet.insert(topfuncname);

        }
    }
    in.close();
}

void PairAnalysisPass::differentialCheck_Refcount(Function *F,
    PathPairs pathpairs,
    int i, int j,
    map<int, set<Value *>> pathpairfuncpairarr,
    set<string> &reportSet){

    if(!F)
        return;
    
    if(pathpairs.getPathNum() == 0)
        return;
    
    if(pathpairfuncpairarr[i].empty() && pathpairfuncpairarr[j].empty())
        return;

    ofstream in;
    in.open("BugReports.txt",ios::app);

    //check if pair func in path j does not show in path i
    for(auto k=pathpairfuncpairarr[j].begin();k!=pathpairfuncpairarr[j].end();k++){

        Value * pairfunccall= *k;//refcount
        CallInst *CV_CAI = dyn_cast<CallInst>(pairfunccall);
        StringRef CV_FName = getCalledFuncName(CV_CAI);

        //Check if pair funcs in path j occur in path i
        if(!findCommonRefcountFunc(pathpairfuncpairarr[i],pairfunccall)){

            auto CV_Peerfunc_Name_set = Ctx->RefcountFuncs[CV_FName];
            bool findtag;

            //检测是否一对pair function都仅仅在一条路径（path j）出现
            //Todo: 考虑pair function出现的顺序
            //Note: 在common head里的不应该被考虑在内,仅匹配head以后的路径
            set<Value *> HeadValues;
            HeadValues.clear();
            BasicBlock *CommonHead = pathpairs.Paths[j].CBChain[0].BB;
            //OP<<"Head: "<<getBlockName(CommonHead)<<"\n";
            for(BasicBlock::iterator i = CommonHead->begin(); i != CommonHead->end(); i++){
                HeadValues.insert(&*i);
                //OP<<"HeadValues: "<< *i <<"\n";
            }

            for(auto it = CV_Peerfunc_Name_set.begin(); it != CV_Peerfunc_Name_set.end();it++){

                findtag = checkPairFuncUse(*it, pathpairfuncpairarr[j],HeadValues);
                if(!findtag){
                    break;
                }
            }

            if(findtag){
                BasicBlock *CommonHead = pathpairs.Paths[j].CBChain[0].BB;
                if(checkCondofCommonHead(F,CommonHead)){
                    //OP << "Stop here2"<<"\n";
                    findtag = false;
                }
                for (BasicBlock::iterator I = CommonHead->begin(),
					IE = CommonHead->end(); I != IE; ++I) {

				    CallInst *CAI = dyn_cast<CallInst>(&*I);
                    if(CAI){
                        StringRef FName = getCalledFuncName(CAI);
                        if(Ctx->RefcountRelatedFuncs.count(FName) == 1)
                            findtag = false;
                    }
                }

            }
            
            //No bug, begin next check loop
            if(!findtag)
                continue;

            if(reportSet.count(F->getName()) == 1)
                continue;

            //Report a bug
            OP<<"\n=============================\n";
            printf("\033[31mWarning: find a potential bug:\033[0m\n");
            OP << "Global Bug num:" << GlobalBugNum++ <<"\n";
            string topfuncname = F->getName();
            //OP << "F: "<<*F<<"\n";
            OP << "File name: "<<getInstFilename(dyn_cast<Instruction>(pairfunccall))<<"\n";
            //OP << "File name: "<<getSourceFuncName(dyn_cast<Instruction>(pairfunccall))<<"\n";
            
            OP << "Function: "<< topfuncname <<"\n";
            OP << "Bug Type: "<< "Refcount bug"<<"\n";
            OP << "-----------------------------\n";
            OP << "Current path pair start at block-"<<getBlockName(pathpairs.startBlock.BB)<<"\n";
            OP << "Refcount function is shown in path \'"<< j <<"\' but not in path \'"<<i<<"\'\n";
            OP << "--Path "<< j <<": ";
            //printSinglePath(pathpairs.Paths[j]);
            OP << " ";
            for(auto it = pathpairs.Paths[j].CBChain.begin(); it != pathpairs.Paths[j].CBChain.end();it++){
                CompoundBlock CBB = *it;
                BasicBlock* BB = CBB.BB;
                OP << "Block-"<<getBlockName(BB)<<" ";
            }
            OP << "\n";
            
            OP << "--Path "<< i <<": ";
            //printSinglePath(pathpairs.Paths[i]);
            OP << " ";
            for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
                CompoundBlock CBB = *it;
                BasicBlock* BB = CBB.BB;
                OP << "Block-"<<getBlockName(BB)<<" ";
            }
            OP << "\n";
            
            OP << "--Branch from line "<<getBranchLineNo(pathpairs.Paths[j])<<"\n";
            OP << "-----------------------------\n";
            OP << "Refcount Func("<<getInstLineNo(dyn_cast<Instruction>(pairfunccall)) <<"): " << string(CV_FName) <<"\n";
            OP<<"=============================\n";
            Ctx->NumBugs++;
            reportSet.insert(topfuncname);
        }

    }//end check

    in.close();
}

void PairAnalysisPass::differentialCheck_ResourceRelease(Function *F,
    PathPairs pathpairs,
    int i, int j,
    map<int, set<CriticalVar>> resourcereleasefuncpairarr,
    std::map<int, set<CriticalVar>> pathpairnormalarr,
    EdgeIgnoreMap edgeIgnoreMap,
    set<string> &reportSet){

    if(!F)
        return;
    
    if(pathpairs.getPathNum() == 0)
        return;
    
    if(resourcereleasefuncpairarr[i].empty() && resourcereleasefuncpairarr[j].empty()){
        return;
    }

    ofstream in;
    in.open("BugReports.txt",ios::app);

    //Check if pair funcs in path j occur in path i
    for(auto k=resourcereleasefuncpairarr[j].begin();k!=resourcereleasefuncpairarr[j].end();k++){
        
        CriticalVar CV= *k;
        Value* releaseoperation = CV.resource_release_inst;
        Value* cirticalvalue = CV.inst;
        Value* getoperation = CV.resource_acq_inst;

        if(!releaseoperation)
            continue;

        //Redundant reports
        if(reportSet.count(F->getName()) != 0)
            continue;

        StringRef CV_FName;
        CallInst *CV_CAI = dyn_cast<CallInst>(releaseoperation);
        if(CV_CAI){
            CV_FName = getCalledFuncName(CV_CAI);
        }
        else{
            CV_FName = releaseoperation->getName();
        }

        bool foundtag = false;
        PointerAnalysisMap structRelations = Ctx->FuncStructResults[F];

        for(auto q = resourcereleasefuncpairarr[i].begin();q!=resourcereleasefuncpairarr[i].end();q++){
            CriticalVar CV_q = *q;
            Value* releaseoperation_q = CV_q.resource_release_inst;
            Value* cirticalvalue_q = CV_q.inst;

            if(releaseoperation_q == releaseoperation){
                foundtag = true;
                break;
            }

            if(cirticalvalue_q == cirticalvalue){
                foundtag = true;
                break;
            }

            if(structRelations.count(cirticalvalue_q)){
                if(structRelations[cirticalvalue_q].count(cirticalvalue)){
                    foundtag = true;
                    break;
                }
            }
        }

        if(foundtag)
            continue;

        foundtag = false;
        set<Value *> resource_acq_set;
        set<Value *> same_release_set;
        resource_acq_set.clear();
        same_release_set.clear();
        for(auto i = Ctx->SecurityOperationSets[F].begin();i!=Ctx->SecurityOperationSets[F].end();i++){
            SecurityOperation SO = *i;
            Value* SOBranch = SO.branch; //first
            Value* SOCheckedValue = SO.checkedValue; //second
            int operationType = SO.operationType;
            if(operationType == ResourceAcquisition){
                if(cirticalvalue == SOCheckedValue)
                    resource_acq_set.insert(SOBranch);
            }

            if(operationType == ResourceRelease){
                if(SOBranch == releaseoperation){
                    same_release_set.insert(SOCheckedValue);
                }
            }
        }

        for(auto it = pathpairs.Paths[j].CBChain.begin(); it != pathpairs.Paths[j].CBChain.end();it++){
            CompoundBlock CBB = *it;
            BasicBlock* BB = CBB.BB;

            for(BasicBlock::iterator i = BB->begin(); i != BB->end(); i++){
                Instruction * inst = dyn_cast<Instruction>(i);
                if(resource_acq_set.count(inst) == 1){
                    foundtag = true;
                    break;
                }
            }
        }

        if(foundtag)
            continue;

        for(auto it = pathpairnormalarr[i].begin();it!=pathpairnormalarr[i].end();it++){
            CriticalVar NV= *it;
            Value *TV = NV.inst;

            CallInst *CAI = dyn_cast<CallInst>(TV);
            if(CAI){
                StringRef calledFName = getCalledFuncName(CAI);
                if(Ctx->EscapeFuncs.count(calledFName)){
                    foundtag = true;
                    break;
                }
            }

            // Detect callback release
            StoreInst *STI = dyn_cast<StoreInst>(TV);
            if(STI){
                Value* vop = STI->getValueOperand();
                auto call = dyn_cast<Function>(vop);
                if(call){
                    if(call->getName().contains("free") || call->getName().contains("release")){
                        foundtag = true;
                        break;
                    }
                }
            }
        }
        
        if(foundtag)
            continue;

        foundtag = false;
        BasicBlock *CommonHead = pathpairs.Paths[j].CBChain[0].BB;
        if(checkCondofCommonHead(F,CommonHead)){
            foundtag = true;
        }

        if(foundtag)
            continue;

        for(auto it = same_release_set.begin(); it != same_release_set.end();it++){
            Value* resource_acq = *it;
            foundtag = checkTargetinCommonHeadCond(resource_acq,CommonHead);
            if(foundtag)
                break;
        }

        if(foundtag)
            continue;        
        
        Instruction *resource_acq = dyn_cast<Instruction>(cirticalvalue);
        if(resource_acq != NULL){
            BasicBlock *resource_acq_bb = resource_acq->getParent();
            if(!checkBlockPairConnectivity(resource_acq_bb,CommonHead,edgeIgnoreMap)){
                continue;
            }
        }  

        if(checkValueRedefine(F,cirticalvalue,CommonHead,edgeIgnoreMap))
            continue;

        //Check value escape to F's arguments
        set<Value *>pathvalueset;
        pathvalueset.clear();
        for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
            CompoundBlock CBB = *it;
            BasicBlock* BB = CBB.BB;
            if(BB == CommonHead)
                continue;
            
            for(BasicBlock::iterator i = BB->begin(); i != BB->end(); i++){
                pathvalueset.insert(&*i);
            }
        }

        if(checkValueEscape(F,cirticalvalue,pathvalueset))
            continue;


        foundtag = false;
        for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
            CompoundBlock CBB = *it;
            BasicBlock* BB = CBB.BB;
            if(BB == CommonHead)
                continue;
            //OP << "Block-"<<getBlockName(BB)<<"\n";
            for(BasicBlock::iterator i = BB->begin(); i != BB->end(); i++){
                CallInst * CAI = dyn_cast<CallInst>(i);
                if(CAI){

                    StringRef BB_FName = getCalledFuncName(CAI);
                    if(BB_FName.empty())
                        continue;

                    if(Ctx->ReleaseFuncSet.count(BB_FName) || checkStringContainSubString(BB_FName,"free")){
                        if(checkValidCaller(cirticalvalue,CAI)){
                            foundtag = true;
                            break;
                        }

                        unsigned argnum = CAI->getNumArgOperands();
                        for(unsigned j=0;j<argnum;j++){
                            Value* arg = CAI->getArgOperand(j);
                            if(structRelations.count(arg)){
                                if(structRelations[arg].count(cirticalvalue)){
                                    foundtag = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
            if(foundtag)
                break;
        }

        if(foundtag)
            continue;
        
        //Report a bug
        OP<<"\n=============================\n";
        printf("\033[31mWarning: find a potential bug:\033[0m\n");
        OP << "Global Bug num:" << GlobalBugNum++ <<"\n";
        string topfuncname = F->getName();
        OP << "File name: "<<getInstFilename(dyn_cast<Instruction>(releaseoperation))<<"\n";
            
        OP << "Function: "<< topfuncname <<"\n";
        OP << "Bug Type: "<< "Missing release"<<"\n";
        OP << "-----------------------------\n";
        OP << "Current path pair start at block-"<<getBlockName(pathpairs.startBlock.BB)<<"\n";
        OP << "Release function is shown in path \'"<< j <<"\' but not in path \'"<<i<<"\'\n";
        OP << "--Path "<< j <<": ";
        OP << " ";
        for(auto it = pathpairs.Paths[j].CBChain.begin(); it != pathpairs.Paths[j].CBChain.end();it++){
            CompoundBlock CBB = *it;
            BasicBlock* BB = CBB.BB;
            OP << "Block-"<<getBlockName(BB)<<" ";
        }
        OP << "\n";
        OP << "--Path "<< i <<": ";
        OP << " ";
        for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
            CompoundBlock CBB = *it;
            BasicBlock* BB = CBB.BB;
            OP << "Block-"<<getBlockName(BB)<<" ";
        }
        OP << "\n";
        OP << "--Branch from line "<<getBranchLineNo(pathpairs.Paths[j])<<"\n";
        OP << "-----------------------------\n";
        OP << "Target value: "<< getValueContent(cirticalvalue) <<"\n";
        //OP << "Alloc point:  "<< getValueContent(getoperation)<<"\n";
        OP << "Release Func("<<getInstLineNo(dyn_cast<Instruction>(releaseoperation)) <<"): " << string(CV_FName) <<"\n";
        //OP << "Critical value: "<< *cirticalvalue <<"\n";
        OP<<"=============================\n";
        Ctx->NumBugs++;
        reportSet.insert(topfuncname);
    }

    in.close();
}

//Used in similarPathAnalysis_singlePathpair
void PairAnalysisPass::differentialCheck_SecurityCheck(Function *F,
    PathPairs pathpairs,
    int i, int j,
    vector<set<Value *>>pathvalueset_vector,
    map<int, set<CriticalVar>> pathpaircriticalarr,
    map<int, set<CriticalVar>> pathpairnormalarr,
    set<string> &reportSet){
    
    if(!F)
        return;
    
    if(pathpairs.getPathNum() == 0)
        return;
    
    if(pathpaircriticalarr[i].empty() && pathpaircriticalarr[j].empty()){
        return;
    }

    ofstream in;
    in.open("BugReports.txt",ios::app);

    set<Value *>normalvalues_of_path_i;
    set<Value *>normalvalues_of_path_j;
    normalvalues_of_path_i.clear();
    normalvalues_of_path_j.clear();

    for(auto it = pathpairnormalarr[i].begin();it!=pathpairnormalarr[i].end();it++){
        CriticalVar CV_normal = *it;
        Value * nromalinst = CV_normal.inst;
        normalvalues_of_path_i.insert(nromalinst);
    }
    for(auto it = pathpairnormalarr[j].begin();it!=pathpairnormalarr[j].end();it++){
        CriticalVar CV_normal = *it;
        Value * nromalinst = CV_normal.inst;
        normalvalues_of_path_j.insert(nromalinst);
    }

    for(auto k = pathpaircriticalarr[j].begin();k!=pathpaircriticalarr[j].end();k++){
        CriticalVar CV_critical = *k;
        Value* checkedvalue = CV_critical.check;
        Value* branchvalue = CV_critical.inst;

        //Currently ignore values source from function arguments
        if(CV_critical.source_from_outside)
            continue;

        if(!CV_critical.getelementptrInfo.empty())
            continue;
        
        if(CV_critical.sourcefuncs.empty())
            continue;

        BasicBlock *CommonHead = pathpairs.Paths[j].CBChain[0].BB;
        if(checkCondofCommonHead(F,CommonHead)){
            // if branch from a switch, ignore this case
            Instruction *Head_TI = CommonHead->getTerminator();
            SwitchInst *SI = dyn_cast<SwitchInst>(Head_TI);
            if(SI)
                continue;
        }


        bool foundtag = false;
        for(BasicBlock::iterator iter = CommonHead->begin(); iter != CommonHead->end(); iter++){
            Instruction * inst = dyn_cast<Instruction>(iter);
            if(inst == branchvalue) {
                foundtag = true;
            }
        }

        if(foundtag)
            continue;

        for(auto p = pathpairnormalarr[i].begin();p!=pathpairnormalarr[i].end();p++){
            CriticalVar CV_normal = *p;

            //Found a normal value should be checked
            //if(CV_normal.source == CV_critical.source){
            //if(findCommonOfSet(CV_normal.sourceset, CV_critical.sourceset)){
            if(findCVSource(CV_normal, CV_critical)){
                //foundtag is false if this is a real bug
                
                for(auto q = pathpairnormalarr[j].begin();q!=pathpairnormalarr[j].end();q++){
                    CriticalVar CV = *q;
                    if(CV_normal.inst == CV.inst){
                        foundtag = true;
                        break;
                    }
                }

                if(foundtag)
                    continue;
                
                //OP << "2Found a normal value should be checked\n";
                //OP << "2source: "<<*(*CV_normal.sourceset.begin())<<"\n";

                for(auto it = pathpaircriticalarr[i].begin();it!=pathpaircriticalarr[i].end();it++){
                    CriticalVar CV_cur = *it;
                    Value* checkedvalue_i = CV_cur.check;

                    if(CV_cur.inst == CV_normal.inst){
                        foundtag = true;
                        break;
                    }

                    //Maybe should add location info here
                    //if(CV_cur.source == CV_normal.source){
                    //if(findCommonOfSet(CV_cur.sourceset, CV_normal.sourceset)){
                    if(findCVSource(CV_normal, CV_cur)){
                        //uOP<<"check\n";
                        //foundtag = true;
                        //break;
                    }
                }
                
                if(foundtag)
                    continue;

                CallInst *NCAI = dyn_cast<CallInst>(CV_normal.inst);
                if(!NCAI)
                    continue;

                //The range should be specified
                if(checkUseChain(CV_normal.inst, pathpairs.Paths[i]))
                    continue;
                
                //Test strategy
                stack<Value *> post_condistions_i; 
                stack<Value *> post_condistions_j; 
                initPostConditions(pathpairs.Paths[i],CV_normal.inst,post_condistions_i);
                initPostConditions(pathpairs.Paths[j],checkedvalue,post_condistions_j);

                //if(post_condistions_i.size() == 0 && post_condistions_j.size() != 0
                if(post_condistions_i.size() == 0 
                 && checkDirectReturn(pathpairs.Paths[i],CV_normal.inst))
                    continue;

                if(reportSet.count(F->getName()) != 0)
                    continue;
                
                if(getInstLineNo(dyn_cast<Instruction>(checkedvalue)) == getInstLineNo(dyn_cast<Instruction>(CV_normal.inst)))
                    continue;

                //if(0 == pathpaircriticalarr[i].count(CV_normal)){
                if(!foundtag){

                    OP<<"\n=============================\n";
                    printf("\033[31mWarning: find a potential bug:\033[0m\n");
                    OP << "Global Bug num:" << GlobalBugNum++ <<"\n";
                    string topfuncname = F->getName();
                    OP << "File name: "<<getInstFilename(dyn_cast<Instruction>(CV_critical.inst))<<"\n";
                    OP << "Function: "<< topfuncname <<"\n";
                    OP << "Bug Type: "<< "Missing check"<<"\n";
                    OP << "-----------------------------\n";
                    OP << "Current path pair start at block-"<<getBlockName(pathpairs.startBlock.BB)<<"\n";
                    OP << "CriticalVar is checked in path \'"<< j <<"\' but not in path \'"<<i<<"\'\n";
                    OP << "--Path "<< j <<": ";
                    OP << " ";
                    for(auto it = pathpairs.Paths[j].CBChain.begin(); it != pathpairs.Paths[j].CBChain.end();it++){
                        CompoundBlock CBB = *it;
                        BasicBlock* BB = CBB.BB;
                        OP << "Block-"<<getBlockName(BB)<<" ";
                    }
                    OP << "\n";
                    OP << "--Path "<< i <<": ";
                    OP << " ";
                    for(auto it = pathpairs.Paths[i].CBChain.begin(); it != pathpairs.Paths[i].CBChain.end();it++){
                        CompoundBlock CBB = *it;
                        BasicBlock* BB = CBB.BB;
                        OP << "Block-"<<getBlockName(BB)<<" ";
                    }
                    OP << "\n";
                    OP << "--Branch from line "<<getBranchLineNo(pathpairs.Paths[j])<<"\n";
                    OP << "-----------------------------\n";
                    OP << "CriticalVar("<<getInstLineNo(dyn_cast<Instruction>(checkedvalue))<<"): "<<getValueContent(checkedvalue)<<"\n";
                    
                    OP << "CriticalSource:\n";
                    for(auto i = CV_critical.sourceset.begin(); i != CV_critical.sourceset.end(); i++){
                        OP << "--Source("<<getInstLineNo(dyn_cast<Instruction>(*i))<<"): "<<getValueContent(*i)<<"\n";
                    }

                    OP << "Sourcefuns:\n";
                    for(auto i = CV_critical.sourcefuncs.begin(); i != CV_critical.sourcefuncs.end(); i++){
                        string funcname = *i;
                        OP << "--" << funcname <<"\n";
                    }

                    OP<<"getelementptr source: \n";
                    for(auto i = CV_critical.getelementptrInfo.begin(); i != CV_critical.getelementptrInfo.end(); i++){
                        OP<<"--Source 1: "<<getValueContent(i->first)<<"\n";
                        for(auto j = i->second.begin(); j!=i->second.end();j++){
                            OP<<"Source 2: "<<getValueContent(*j)<<"\n";
                        }
                    }
                    
                    OP << "CheckInst("<<getInstLineNo(dyn_cast<Instruction>(CV_critical.check))<< "): "<<getValueContent(CV_critical.check)<<"\n";
                    OP << "-----------------------------\n";
                    OP << "NormalInst("<<getInstLineNo(dyn_cast<Instruction>(CV_normal.inst))<<"): "<< getValueContent(CV_normal.inst)<<"\n";
                    OP << "NormalSource:\n";
                    for(auto i = CV_normal.sourceset.begin(); i != CV_normal.sourceset.end(); i++){
                        OP << "--Source("<<getInstLineNo(dyn_cast<Instruction>(*i))<<"): "<<getValueContent(*i)<<"\n";
                    }

                    OP << "Sourcefuns:\n";
                    for(auto i = CV_normal.sourcefuncs.begin(); i != CV_normal.sourcefuncs.end(); i++){
                        string funcname = *i;
                        OP << "--" << funcname <<"\n";
                    }

                    OP<<"getelementptr source: \n";
                    for(auto i = CV_normal.getelementptrInfo.begin(); i != CV_normal.getelementptrInfo.end(); i++){
                        OP<<"--Source 1: "<<getValueContent(i->first)<<"\n";
                        for(auto j = i->second.begin(); j!=i->second.end();j++){
                            OP<<"Source 2: "<<getValueContent(*j)<<"\n";
                        }
                    }

                    OP<<"=============================\n";
                    Ctx->NumBugs++;

                    reportSet.insert(topfuncname);
                }
            }
        }

    }//end check
    in.close();

}