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
#include <algorithm>

#include "PairAnalysis.h"

using namespace llvm;

//Debug function
void PairAnalysisPass::showEdgeIgnoreMap(EdgeIgnoreMap edgeIgnoreMap){
    if(edgeIgnoreMap.empty()){
        OP<<"Empty map\n";
        return;
    }
    OP<<"EdgeIgnoreMap: \n";
    for(auto it = edgeIgnoreMap.begin(); it != edgeIgnoreMap.end(); it++){
        CFGEdge edge = it->first;
        Instruction *firstI = edge.first;
        BasicBlock *secondbb = edge.second;
        BasicBlock *firstbb = firstI->getParent();
        OP << "Block-"<<getBlockName(firstbb)<<" -> "<<getBlockName(secondbb)<<"\n";
    }

}

//Debug function
void PairAnalysisPass::printSinglePath(SinglePath singlepath){
    if(singlepath.getPathLength()==0)
        return;

    OP << " ";
    for(auto i = singlepath.CBChain.begin(); i != singlepath.CBChain.end();i++){
        CompoundBlock CBB = *i;
        BasicBlock* BB = CBB.BB;
        OP << "Block-"<<getBlockName(BB)<<" ";
    }

    OP << "\n";
}

unsigned PairAnalysisPass::getBranchLineNo(SinglePath singlepath){
    if(singlepath.getPathLength()==0)
        return -1;
    
    CompoundBlock firstCB = *(singlepath.CBChain.begin());
    BasicBlock* firstBB = firstCB.BB;
    auto TI = firstBB->getTerminator();

    return getInstLineNo(TI);
}

//Return true if this block (bb) is a return block
bool PairAnalysisPass::checkReturnBlock(BasicBlock *bb, EdgeIgnoreMap edgeIgnoreMap){
    if(!bb)
        return false;

    auto TI = bb->getTerminator();
    int NumSucc = TI->getNumSuccessors();
    bool result = false;

    if(NumSucc == 0)
        return true;
    else {

        int num = NumSucc;
        for(int i = 0; i < NumSucc; i++){

            BasicBlock *succblock = TI->getSuccessor(i);
            CFGEdge edge = make_pair(TI,succblock);
            if(1 == edgeIgnoreMap.count(edge)){
                num--;
            }
        }

        if(num == 0)
            return true;
        else 
            return false;
    }
}

//Find the top block
BasicBlock * PairAnalysisPass::findTopBlock(std::set<BasicBlock *> blockset, 
    ConnectGraph connectGraph){
    
    if(blockset.empty() || connectGraph.empty())
        return NULL;
    
    for(auto i = blockset.begin(); i != blockset.end();i++){

        BasicBlock * bb1 = *i;
        bool top = true;
        for(auto j = blockset.begin(); j != blockset.end();j++){
            BasicBlock *bb2 = *j;

            if(!checkBlockAToB_Version2(bb1, bb2, connectGraph)){
                top = false;
                break;
            }
        }
        if(top)
            return bb1;
    }

    return NULL;
}

BasicBlock * PairAnalysisPass::findTopBlock(std::set<BasicBlock *> blockset){
    
    if(blockset.empty())
        return NULL;
    
    for(auto i = blockset.begin(); i != blockset.end();i++){

        BasicBlock * bb1 = *i;
        bool top = true;

        //Top block can connect to all other blocks
        for(auto j = blockset.begin(); j != blockset.end();j++){
            BasicBlock *bb2 = *j;

            if(!checkBlockPairConnectivity(bb1, bb2)){
                top = false;
                break;
            }
        }
        if(top)
            return bb1;
    }

    return NULL;
}

//Find the bottom block
BasicBlock * PairAnalysisPass::findBottomBlock(std::set<BasicBlock *> blockset){
    
    if(blockset.empty())
        return NULL;

    for (auto i = blockset.begin(); i != blockset.end(); i++){
        
        BasicBlock * bb1 = *i;
        bool bottom = true;

        //Bottom cannot connect to all other blocks
        for (auto j = blockset.begin(); j != blockset.end(); j++){
            BasicBlock * bb2 = *j;
            if(bb1 == bb2)
                continue;
            
            if(checkBlockPairConnectivity(bb1, bb2)){
                bottom = false;
                break;
            }
        }

        if(bottom)
            return bb1;
    }

    return NULL;

}

void PairAnalysisPass::initGlobalPathMap(std::vector<PathPairs> PathGroup,
    std::map<BasicBlock *, PathPairs> &GlobalPathMap){
    
    GlobalPathMap.clear();

    if(PathGroup.empty())
        return;
    
    for(int i=0; i<PathGroup.size();i++){

        PathPairs curpathpairs = PathGroup[i];
        BasicBlock * startBlock = curpathpairs.Paths[0].CBChain[0].BB;

        GlobalPathMap[startBlock] = curpathpairs;
    }
}


//Check if there is a path from fromBB to toBB 
bool PairAnalysisPass::checkBlockPairConnectivity(
    BasicBlock* fromBB, 
    BasicBlock* toBB,
    EdgeIgnoreMap edgeIgnoreMap){

    if(fromBB == NULL || toBB == NULL)
        return false;
    
    //Use BFS to detect if there is a path from fromBB to toBB
    std::list<BasicBlock *> EB; //BFS record list
    std::set<BasicBlock *> PB; //Global value set to avoid loop
    EB.push_back(fromBB);

    while (!EB.empty()) {

        BasicBlock *TB = EB.front(); //Current checking block
		EB.pop_front();

		if (PB.find(TB) != PB.end())
			continue;
		PB.insert(TB);

        //Found a path
        if(TB == toBB)
            return true;

        auto TI = TB->getTerminator();

        for(BasicBlock *Succ: successors(TB)){

            CFGEdge edge = make_pair(TI,Succ);
            if(edgeIgnoreMap.count(edge) != 0){
                continue;
            }

            EB.push_back(Succ);
        }

    }//end while

    return false;
}

//Check if there is a path from fromBB to toBB 
bool PairAnalysisPass::checkBlockPairConnectivity(
    BasicBlock* fromBB, 
    BasicBlock* toBB){

    if(fromBB == NULL || toBB == NULL)
        return false;
    
    //Use BFS to detect if there is a path from fromBB to toBB
    std::list<BasicBlock *> EB; //BFS record list
    std::set<BasicBlock *> PB; //Global value set to avoid loop
    EB.push_back(fromBB);

    while (!EB.empty()) {

        BasicBlock *TB = EB.front(); //Current checking block
		EB.pop_front();

		if (PB.find(TB) != PB.end())
			continue;
		PB.insert(TB);

        //Found a path
        if(TB == toBB)
            return true;

        auto TI = TB->getTerminator();

        for(BasicBlock *Succ: successors(TB)){

            EB.push_back(Succ);
        }

    }//end while

    return false;
}

//Get the condition of a branch inst
//We expect a load inst here, otherwise return null
LoadInst * PairAnalysisPass::getBranchCondition(
    Instruction *TI){

    if(!TI)
        return NULL;
    
    Value *Cond = NULL;
    if (isa<BranchInst>(TI) || isa<SwitchInst>(TI)) {
        
        BranchInst *BI = dyn_cast<BranchInst>(TI);
		SwitchInst *SI = NULL;
		if (BI) {
            if(BI->isConditional())
			    Cond = BI->getCondition();
		} 
		else {
			SI = dyn_cast<SwitchInst>(TI);
			Cond = SI->getCondition();
		}
    }

    if(Cond == NULL)
        return NULL;

    ICmpInst *ICI = dyn_cast<ICmpInst>(Cond);
    TruncInst *TCI = dyn_cast<TruncInst>(Cond);
    Value *CondTarget = NULL;
    if(ICI){
        auto oprand0 = ICI->getOperand(0);
        auto oprand1 = ICI->getOperand(1);

        if(isConstant(oprand0) && !isConstant(oprand1)){
            CondTarget = oprand1;
        }
        else if(isConstant(oprand1) && !isConstant(oprand0)){
            CondTarget = oprand0;
        }
    }
    else if(TCI){
        CondTarget = TCI->getOperand(0);
    }
    else{
        return NULL;
    }

    if(CondTarget == NULL)
        return NULL;
    
    LoadInst* LI = dyn_cast<LoadInst>(CondTarget);
    if(!LI)
        return NULL;

    return LI;
}

//Check if the branch condition is the argument of function F
//Return true if the branch condition is the argument of F
bool PairAnalysisPass::checkCondofCommonHead(Function *F, BasicBlock* CommonHead){

    if(!F || !CommonHead)
        return false;
    
    if(F->arg_size() == 0)
        return false;
    
    //Init the arguments set of function F
    set<Value *>argset;
    argset.clear();
    for(auto it = F->arg_begin(); it != F->arg_end();it++){
        argset.insert(it);
    }
    
    //Find the branch inst of CommonHead
    //Then get the condition of this branch instruction
    Value *Cond = NULL;
    for(BasicBlock::iterator i = CommonHead->begin(); 
        i != CommonHead->end(); i++){
            
        Instruction * Inst = dyn_cast<Instruction>(i);
        if(isa<BranchInst>(Inst) || isa<SwitchInst>(Inst)){

            BranchInst *BI = dyn_cast<BranchInst>(Inst);
            SwitchInst *SwI = dyn_cast<SwitchInst>(Inst);

            if(BI){
                Cond = BI->getCondition();
            }
            else{
                Cond = SwI->getCondition();
            }
        }
    }

    if(Cond == NULL)
        return false;
    
    if(argset.count(Cond) == 1){
        //OP << "found at first\n";
        return true;
    }

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
	EV.push_back(Cond);
    
    while (!EV.empty()) {

        Value *TV = EV.front(); //Current checking value
		EV.pop_front();

        if(argset.count(TV) == 1){    
            return true;
        }

        //Global variable is also ignored
        if(isa<GlobalValue>(TV) || isa<GlobalVariable>(TV))
            return true;
        
        if (PV.find(TV) != PV.end())
			continue;

		PV.insert(TV);
        Instruction *I = dyn_cast<Instruction>(TV);
        if(!I)
            continue;
        
        ///////////////////////////////////////////////
        // The value is a icmp instruction.
        ///////////////////////////////////////////////
		ICmpInst *ICI = dyn_cast<ICmpInst>(TV);
		if (ICI){
            auto oprand0 = I->getOperand(0);
            auto oprand1 = I->getOperand(1);

            if(isConstant(oprand0) && !isConstant(oprand1)){
                EV.push_back(oprand1);
            }
            else if(isConstant(oprand1) && !isConstant(oprand0)){
                EV.push_back(oprand0);
            }
            else if(!isConstant(oprand1) && !isConstant(oprand0)){
                EV.push_back(oprand0);
                EV.push_back(oprand1);   
            }
            
			continue;
        }

        ///////////////////////////////////////////////
        // The value (%TV) is a load: %TV = load i32, i32* %LPO
        ///////////////////////////////////////////////
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        if(LI){

            Value *LPO = LI->getPointerOperand();
            EV.push_back(LPO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a getelementptr instruction.
        ///////////////////////////////////////////////
		/*GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){
            //The struct ptr
            Value *PO = GEP->getPointerOperand();
            EV.push_back(PO);
            continue;
        }*/

        CallInst *CAI = dyn_cast<CallInst>(TV);
        if(CAI){

            StringRef FName = getCalledFuncName(CAI);
            if(1 == Ctx->MemberGetFuncs.count(FName)){
                Value *arg = CAI->getArgOperand(0);
                EV.push_back(arg);
            }
            else if(FName.contains("_get_drvdata")){
                Value *arg = CAI->getArgOperand(0);
                EV.push_back(arg);
            }
            else if(Ctx->EscapeFuncs.count(FName)){
                return true;
            }

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a single operation instruction.
        ///////////////////////////////////////////////
        auto opcodeName = I->getOpcodeName();
        if(1 == Ctx->SingleOperandInsts.count(opcodeName)){

            Value* op0 = I->getOperand(0);
            if(!isConstant(op0))
                EV.push_back(op0);

            continue;
        }
    }

    return false;
}

bool PairAnalysisPass::checkTargetinCommonHeadCond(Value *targetvar, BasicBlock* CommonHead){

    if(!targetvar || !CommonHead)
        return false;

    set<Value *> targetvarSet;
    targetvarSet.clear();
    targetvarSet.insert(targetvar);

    recheck:
    //First check store inst in CommonHead
    for(BasicBlock::iterator i = CommonHead->begin(); 
        i != CommonHead->end(); i++){

        BitCastInst *BCI = dyn_cast<BitCastInst>(i);
        if(BCI){
            Value *op = BCI->getOperand(0);
            if(targetvarSet.count(op) && !targetvarSet.count(BCI)){
                targetvarSet.insert(BCI);
                goto recheck;
            }
            continue;
        }
           
        StoreInst *STI = dyn_cast<StoreInst>(i);
        if(STI){
            Value* vop = STI->getValueOperand();
            Value* pop = STI->getPointerOperand();
            if(targetvarSet.count(pop) && !targetvarSet.count(vop)){
                targetvarSet.insert(vop);
                goto recheck;
            }
            continue;
        }
    }

    Value *Cond = NULL;
    Instruction *TI = CommonHead->getTerminator();

    if (isa<BranchInst>(TI) || isa<SwitchInst>(TI)) {
        
        BranchInst *BI = dyn_cast<BranchInst>(TI);
		SwitchInst *SI = NULL;
		if (BI) {
            if(BI->isConditional())
			    Cond = BI->getCondition();
		} 
		else {
			SI = dyn_cast<SwitchInst>(TI);
			Cond = SI->getCondition();
		}
    }

    if(Cond == NULL)
        return false;

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
	EV.push_back(Cond);
    
    while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();

        if(targetvarSet.count(TV)){
            return true;
        }
            
        if (PV.find(TV) != PV.end())
			continue;

		PV.insert(TV);
        Instruction *I = dyn_cast<Instruction>(TV);
        if(!I)
            continue;
        
        ///////////////////////////////////////////////
        // The value is a icmp instruction.
        ///////////////////////////////////////////////
		ICmpInst *ICI = dyn_cast<ICmpInst>(TV);
		if (ICI){
            auto oprand0 = I->getOperand(0);
            auto oprand1 = I->getOperand(1);

            if(isConstant(oprand0) && !isConstant(oprand1)){
                EV.push_back(oprand1);
            }
            else if(isConstant(oprand1) && !isConstant(oprand0)){
                EV.push_back(oprand0);
            }
            
			continue;
        }

        ///////////////////////////////////////////////
        // The value (%TV) is a load: %TV = load i32, i32* %LPO
        ///////////////////////////////////////////////
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        if(LI){

            Value *LPO = LI->getPointerOperand();
            EV.push_back(LPO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a getelementptr instruction.
        ///////////////////////////////////////////////
		GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){

            //The struct ptr
            Value *PO = GEP->getPointerOperand();
            EV.push_back(PO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a phi node.
        ///////////////////////////////////////////////
        PHINode *PN = dyn_cast<PHINode>(TV);
        if(PN){
            for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                
                //PHI sets this value according to inBB
                Value *IV = PN->getIncomingValue(i); 
                EV.push_back(IV);
            }
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a bitcast.
        ///////////////////////////////////////////////
        BitCastInst *BCI = dyn_cast<BitCastInst>(TV);
        if(BCI){
            Value *op = BCI->getOperand(0);
            EV.push_back(op);
            continue;
        }

        CallInst *CAI = dyn_cast<CallInst>(TV);
        if(CAI){
            StringRef FName = getCalledFuncName(CAI);
            if(FName == "IS_ERR_OR_NULL" || FName == "IS_ERR"){
                Value* arg = CAI->getArgOperand(0);
                //OP<<"arg: "<<*arg << "\n";
                EV.push_back(arg);
            }
            continue;
        }        
    }

    return false;
}

//Check if there is a branch can lead to release point before commonhead
bool PairAnalysisPass::checkPreReleaseBranch(Function *F, 
    BasicBlock* CommonHead, Value* releaseoperation, 
    EdgeIgnoreMap edgeIgnoreMap){
    
    if(!F || !CommonHead || !releaseoperation)
        return false;
    
    //收集所有commonhead之前的block
    set<BasicBlock*> PreBBSet;
    PreBBSet.clear();
    std::list<BasicBlock *> EB; //BFS record list
    std::set<BasicBlock *> PB; //Global block set to avoid loop
    EB.clear();
    PB.clear();
	EB.push_back(CommonHead);
    
    while (!EB.empty()) {
        BasicBlock *TB = EB.front(); //Current checking block
		EB.pop_front();
        
        if (PB.find(TB) != PB.end())
			continue;

		PB.insert(TB);
        for (BasicBlock *Pred : predecessors(CommonHead)) {
            Instruction *TI = Pred->getTerminator();
            CFGEdge edge = make_pair(TI,CommonHead);
            if(edgeIgnoreMap.count(edge)!= 0){
                continue;
            }

            PreBBSet.insert(Pred);
            EB.push_back(Pred);
        }
    }
    
    for (BasicBlock *Pred : predecessors(CommonHead)) {
        Instruction *TI = Pred->getTerminator();
        CFGEdge edge = make_pair(TI,CommonHead);
        pair<CFGEdge,int> value(edge,1);
        edgeIgnoreMap.insert(value);
    }

    Instruction *RI = dyn_cast<Instruction>(releaseoperation);
    BasicBlock *releasebb = RI->getParent();

    for(auto it = PreBBSet.begin(); it != PreBBSet.end();it++){
        BasicBlock* bb = *it;
        if(checkBlockPairConnectivity(bb,releasebb,edgeIgnoreMap)){
            return true;
        }
    }

    return false;
}

void PairAnalysisPass::initPostConditions(SinglePath path, 
    Value* target_V, stack<Value *> &post_condistions){

    bool collecttag = false;
    BasicBlock* lastbb = path.getEndBlock();
    for(auto it = path.CBChain.begin(); it != path.CBChain.end();it++){
        CompoundBlock CBB = *it;
        BasicBlock* BB = CBB.BB;
        if(BB == lastbb)
            continue;

        for(BasicBlock::iterator iter = BB->begin(); iter != BB->end(); iter++){
            if((&*iter) == target_V){
                collecttag = true;
                continue;
            }

            if(collecttag == false)
                continue;

            CallInst * cinst = dyn_cast<CallInst>(iter);
            if(cinst) {
                StringRef FName = getCalledFuncName(cinst);
                if (Ctx->DebugFuncs.count(FName) == 1)
                    continue;
                post_condistions.push(cinst);
            }

            //Consider other instructions
            ICmpInst *ICI = dyn_cast<ICmpInst>(iter);
            if(ICI) {
                post_condistions.push(ICI);
            }
        }
    }

}

bool PairAnalysisPass::checkDirectReturn(SinglePath path, Value* normalinst){

    if(!normalinst)
        return false;

    Instruction *CAI = dyn_cast<Instruction>(normalinst);
    if(!CAI)
        return false;
    
    BasicBlock* pathlastbb = path.getEndBlock();
    auto *pathlastbb_TI = pathlastbb->getTerminator();

    if(pathlastbb_TI->getNumSuccessors() == 0){
        BasicBlock* CAI_Parrent = CAI->getParent();
        if(CAI_Parrent->getTerminator()->getNumSuccessors() == 1) {
            if(CAI_Parrent->getTerminator()->getSuccessor(0) == pathlastbb)
                return true;
        }
    }

    return false;

}