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


//Find if two criticalvars share the same source
bool PairAnalysisPass::findCVSource(CriticalVar CVA, CriticalVar CVB){
    
    bool result = true;

    //Share common source functions
    if(findCommonOfSet(CVA.sourcefuncs, CVB.sourcefuncs)) {
        //We also need to check the getelementptrInfo here
        goto check_getelementptrInfo;
    }
    
    //First make sure CVA and CVB shares the same root source values
    result = findCommonOfSet(CVA.sourceset, CVB.sourceset);
    
    if(result == false)
        return false;

    check_getelementptrInfo:
    
    //Second make sure the getelementptrInfo is the same (not strict)
    if(CVA.getelementptrInfo.size() == 0 && CVB.getelementptrInfo.size() == 0)
        return true;
    
    set<Value *> eleSet_A, eleSet_B;
    eleSet_A.clear();
    eleSet_B.clear();
    for(auto i = CVA.getelementptrInfo.begin(); i!=CVA.getelementptrInfo.end();i++){
        Value* CVA_first = i->first;
        eleSet_A.insert(CVA_first);
    }
    for(auto i = CVB.getelementptrInfo.begin(); i!=CVB.getelementptrInfo.end();i++){
        Value* CVB_first = i->first;
        eleSet_B.insert(CVB_first);
    }
    if(!findCommonOfSet(eleSet_A,eleSet_B))
        return false;

    bool foundtag = true;
    for(auto i = CVA.getelementptrInfo.begin(); i!=CVA.getelementptrInfo.end();i++){
        Value* CVA_first = i->first;
        if(CVB.getelementptrInfo.count(CVA_first)==0){
            continue;
        }
        else{
            if(CVA.getelementptrInfo[CVA_first] != CVB.getelementptrInfo[CVA_first]){
                foundtag = false;
                break;
            }
        }
    }
    result = foundtag;
    //Todo: use Alias

    return result;
}

//Return true if this value is checked
bool PairAnalysisPass::checkUseChain(Value *V, SinglePath path){
    if(!V)
        return false;

    Instruction *I = dyn_cast<Instruction>(V);
    if(!I)
        return false;
    
    list<Value *> checkset;
    set<Value *> checkedset;

    checkset.push_back(V);
    while (!checkset.empty()) {

        Value *TV = checkset.front(); //Current checking value
		checkset.pop_front();

        if(checkedset.count(TV))
            continue;
        
        checkedset.insert(TV);

        ICmpInst *ICI = dyn_cast<ICmpInst>(TV);
        if(ICI) {
            auto oprand0 = ICI->getOperand(0);
			auto oprand1 = ICI->getOperand(1);
            if(!isConstant(oprand0) && !isConstant(oprand1))
                continue;

            BasicBlock* parentbb = ICI->getParent();
            if(path.checkBlockInPath(parentbb))
                return true;
            continue;
        }

        BranchInst *BI = dyn_cast<BranchInst>(TV);
        if(BI) {
            return true;
        }
        
        for(User *U : TV->users()){

            ICmpInst *ICI = dyn_cast<ICmpInst>(U);
            if(ICI) {

                auto oprand0 = ICI->getOperand(0);
                auto oprand1 = ICI->getOperand(1);

                BasicBlock* parentbb = ICI->getParent();
                if(path.checkBlockInPath(parentbb))
                    return true;
                continue;
            }

            SelectInst *SI = dyn_cast<SelectInst>(U);
            if(SI) {
                Value *Cond = SI->getCondition();
                if(Cond == TV) {
                    //OP<<"select: "<<*SI <<"\n";
                    BasicBlock* parentbb = SI->getParent();
                    if(path.checkBlockInPath(parentbb))
                        return true;
                    continue;
                }
            }

            SwitchInst *SWI = dyn_cast<SwitchInst>(U);
            if(SWI){
                Value *Cond = SWI->getCondition();
                if(Cond == TV){
                    //OP<<"switch: "<<*SWI<<"\n";
                    BasicBlock* parentbb = SWI->getParent();
                    if(path.checkBlockInPath(parentbb))
                        return true;
                    continue;
                }
            }

            Instruction *I = dyn_cast<Instruction>(U);
            if(I){
                auto opcodeName = I->getOpcodeName();
                if( strcmp(opcodeName, "and") == 0 || strcmp(opcodeName, "or") == 0){
                    checkset.push_back(U);
                    continue;
                }
            }
            
            CallInst *CAI = dyn_cast<CallInst>(U);
            if(CAI){
                StringRef FName = getCalledFuncName(CAI);
                if(FName == "IS_ERR_OR_NULL" || FName == "IS_ERR"){
                    checkset.push_back(U);
                    continue;
                }
            }

            ExtractValueInst *EVI = dyn_cast<ExtractValueInst>(U);
            if(EVI){
                checkset.push_back(U);
                continue;
            }

            BranchInst *BI = dyn_cast<BranchInst>(U);
            if(BI) {
                //OP<<"br: "<<*BI <<"\n";
                BasicBlock* parentbb = BI->getParent();
                if(path.checkBlockInPath(parentbb))
                    return true;
                continue;
            }

            /*StoreInst *STI = dyn_cast<StoreInst>(U);
            if(STI) {
                //TODO : resolve this case
                return true;
                Value* pop = STI->getPointerOperand();
                BasicBlock* pbb = STI->getParent();
                for(BasicBlock::iterator i = pbb->begin(); i != pbb->end(); i++){

                    auto loadinst = dyn_cast<LoadInst>(i);
                    if(loadinst){
                        Value *LPO = loadinst->getPointerOperand();
                        if(LPO == pop)
                            checkset.push_back(loadinst);
                    }

                }
                continue;
            }*/

            BitCastInst *BCI = dyn_cast<BitCastInst>(U);
            IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(U);
            PtrToIntInst *PTII = dyn_cast<PtrToIntInst>(U);
            ZExtInst *ZEI = dyn_cast<ZExtInst>(U);
            PHINode *PN = dyn_cast<PHINode>(U);
            if(BCI || ITPI || PTII || ZEI || PN){
                checkset.push_back(U);
                continue;
            }
        }
    }

    return false;
}

//Initialize pathvalueset (singlepath)
void PairAnalysisPass::initPathValueSet(SinglePath singlepath,
    std::set<Value *> &pathvalueset){
    
    pathvalueset.clear();
    
    if(singlepath.getPathLength()==0)
        return;
    
    for(auto j = singlepath.CBChain.begin(); j != singlepath.CBChain.end();j++){

        CompoundBlock CBB = *j;
        BasicBlock* BB = CBB.BB;

        for(BasicBlock::iterator i = BB->begin(); i != BB->end(); i++){
            pathvalueset.insert(&*i);
        }
    }
}

// Find same-origin variables from the given variable
void PairAnalysisPass::findSameVariablesFrom(Function *F,
        CriticalVar &criticalvar,
        std::set<CFGEdge>pathedgeset
        ) {

	//Value* VSource = V;
	std::set<Value *> PV; //Global value set to avoid loop
	std::list<Value *> EV; //BFS record list

	PV.clear();
	EV.clear();
	EV.push_back(criticalvar.inst);

	while (!EV.empty()) {

		Value *TV = EV.front(); //Current checking value
		EV.pop_front();

		if (PV.find(TV) != PV.end())
			continue;
		PV.insert(TV);
        
        //The source is a global value
        auto globalvar = dyn_cast<GlobalValue>(TV);
        if(globalvar){
            criticalvar.sourceset.insert(TV);
            criticalvar.source_from_outside = true;
            continue;
        }
        
        //The source is function parameter
        if (isa<Argument>(TV)) {
            criticalvar.sourceset.insert(TV);
            criticalvar.source_from_outside = true;
            continue;
        }
    
        Instruction *I = dyn_cast<Instruction>(TV);
        if(!I)
            continue;

        ///////////////////////////////////////////////
        // The value (%TV) is a load: %TV = load i32, i32* %LPO
        // The value is a load. Let's find out the previous stores.
        ///////////////////////////////////////////////
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        if(LI){

            Value *LPO = LI->getPointerOperand();
            EV.push_back(LPO);

            //Get all stored values
            for(User *U : LPO->users()){
                StoreInst *STI = dyn_cast<StoreInst>(U);
                if(STI){
                    
                    Value* vop = STI->getValueOperand(); // store vop to pop
                    Value* pop = STI->getPointerOperand();
                    if(pop == LPO)
                        EV.push_back(vop);
                }
            }

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a getelementptr instruction.
        // We need to stop here
        ///////////////////////////////////////////////
		GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(TV);
        if(GEP){

            //The struct ptr
            Value *PO = GEP->getPointerOperand();

            auto numindices = GEP->getNumIndices();
            //OP << "numindices: "<<numindices<<"\n";

            vector<Value*> GEPInfo;
            GEPInfo.clear();

            for(int i = 0;i<numindices;i++){
                Value* indice = GEP->getOperand(i+1);
                GEPInfo.push_back(indice);
            }
            pair<Value*, vector<Value*>> value(PO,GEPInfo);
            criticalvar.getelementptrInfo.insert(value);

            EV.push_back(PO);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a call instruction.
        // Function could be a void func (no return or assign) 
        ///////////////////////////////////////////////
		CallInst *CAI = dyn_cast<CallInst>(TV);
		if(CAI){

            StringRef FName = getCalledFuncName(CAI);

            //Ignore llvm debug funcs
            if(1 == Ctx->DebugFuncs.count(FName)){
                //OP << "Found a debug funcs: "<<FName<<"\n";
                continue;
            }

            if(FName == "PTR_ERR" || FName == "ERR_PTR" || FName == "IS_ERR"){
                EV.push_back(CAI->getArgOperand(0));
                continue;
            }

            //Todo: consider copy.memwrite functions

            //Consider the function
            criticalvar.sourceset.insert(TV);
            if(FName != "")
                criticalvar.sourcefuncs.insert(FName);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a branch instruction. (br)
        ///////////////////////////////////////////////
        BranchInst *BI = dyn_cast<BranchInst>(TV);
        if(BI){

            if (BI->getNumSuccessors() < 2)
				continue;

            auto CD = BI->getCondition(); //test can be icmp

            EV.push_back(CD);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a select instruction.  
        // %27 = select i1 %26, i32 %20, i32 %22
        ///////////////////////////////////////////////
        SelectInst *SI = dyn_cast<SelectInst>(TV);
        if(SI){

            Value *Cond = SI->getCondition(); //%26
            //Value* Truevalue = SI->getTrueValue(); //%20
            //Value* Falsevalue = SI->getFalseValue(); //%22
            EV.push_back(Cond);
            continue;
        }

        ///////////////////////////////////////////////
        // The value is a switch instruction.
        ///////////////////////////////////////////////
        SwitchInst *SWI = dyn_cast<SwitchInst>(TV);
        if(SWI){

            if (SWI->getNumSuccessors() < 2)
					continue;

            auto CD = SWI->getCondition();

            EV.push_back(CD);

            continue;
        }

        ///////////////////////////////////////////////
        // The value is a icmp instruction.
        // Only consider comparison with constant
        ///////////////////////////////////////////////
		ICmpInst *ICI = dyn_cast<ICmpInst>(TV);
		if (ICI){
            
            //null is also a const
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
        // Single operand instructions.
        // Just pick the pre value.
        ///////////////////////////////////////////////
        auto opcodeName = I->getOpcodeName();
        if(1 == Ctx->SingleOperandInsts.count(opcodeName)){

            //Get the operated var as the source
            //Only have op0
            Value *op = I->getOperand(0);

            EV.push_back(op);
			continue;
        }

        /*------------------------Multiple sources inst (begin)------------------------*/
        ///////////////////////////////////////////////
        // The value is a phinode. 
        // %40 = phi i8* [ %21, %28 ], [ %21, %35 ], ..
        ///////////////////////////////////////////////
		PHINode *PN = dyn_cast<PHINode>(TV);
        if(PN){

            // Check each incoming value.
			for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                
                //PHI sets this value according to inBB
                Value *IV = PN->getIncomingValue(i); // %21 %21
                BasicBlock *inBB = PN->getIncomingBlock(i); // %28 %35
                auto inTi = inBB->getTerminator();
                CFGEdge edge = make_pair(inTi,inBB);

                //Path sensitive source check
                if(!pathedgeset.count(edge))
                    continue;

                //All of the above values/blocks are out of current block
                //But not sure if they are out of current path
                if(!isConstant(IV)){
                    EV.push_back(IV);
                }
            }
            continue;
        }

        /*------------------------Multiple sources inst (end)------------------------*/

        //Resolve binary operation
        
        if(1 == Ctx->BinaryOperandInsts.count(opcodeName)){

            criticalvar.sourceset.insert(TV);
            continue;

            Value* op0 = I->getOperand(0);
            Value* op1 = I->getOperand(1);

            if(!isConstant(op0) && isConstant(op1)){
                EV.push_back(op0);
                continue;
            }
            else if(!isConstant(op1) && isConstant(op0)){
                EV.push_back(op1);
                continue;
            }
            continue;
        }
	}
}

////////////////////////////////////////////////////////
//Missing Resource Release check related
////////////////////////////////////////////////////////
bool PairAnalysisPass::checkValueEscape(Function *F, 
    Value *cirticalvalue, 
    set<Value *>pathvalueset){
    
    if(!F || !cirticalvalue)
        return false;
    
    //First collect all F arguments related values
    if(F->arg_size() == 0)
        return false;

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    set<Value *> arg_origin_values;
    EV.clear();
    PV.clear();
	arg_origin_values.clear();
    for(auto it = F->arg_begin(); it != F->arg_end();it++){
        Type *arg_type = it->getType();
        if(arg_type->isPointerTy() || arg_type->isStructTy()){
            EV.push_back(it);
            arg_origin_values.insert(it);
        }
    }
    
    //Find all arg origin values
    while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();
            
        if (PV.find(TV) != PV.end())
			continue;
        PV.insert(TV);

        for(User *U : TV->users()){
            if(U == TV)
                continue;

            Type *U_type = U->getType();
            if(!U_type->isPointerTy() && !U_type->isStructTy())
                continue;
            
            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U);
            if(GEP){
                EV.push_back(U);
                arg_origin_values.insert(U);
                continue;
            }

            LoadInst* LI = dyn_cast<LoadInst>(U);
            if(LI){
                EV.push_back(U);
                arg_origin_values.insert(U);
                continue;
            }

            BitCastInst *BCI = dyn_cast<BitCastInst>(U);
            if(BCI){
                EV.push_back(U);
                arg_origin_values.insert(U);
                continue;
            }

            PHINode *PN = dyn_cast<PHINode>(U);
            if(PN){
                EV.push_back(U);
                arg_origin_values.insert(U);
                continue;
            }

            CallInst *CAI = dyn_cast<CallInst>(U);
            if(CAI){
                //Todo
            }
        }
    }

    EV.clear();
    PV.clear();
    EV.push_back(cirticalvalue);
     while (!EV.empty()) {
        Value *TV = EV.front(); //Current checking value
		EV.pop_front();
            
        if (PV.find(TV) != PV.end())
			continue;
        PV.insert(TV);

        for(User *U : TV->users()){
            if(U == TV)
                continue;
            
            BitCastInst *BCI = dyn_cast<BitCastInst>(U);
            if(BCI){
                EV.push_back(BCI);
                continue;
            }

            StoreInst *STI = dyn_cast<StoreInst>(U);
            if(STI){
                Value* vop = STI->getValueOperand();
                Value* pop = STI->getPointerOperand();
                
                //把U存到了pop里面，查看pop是不是和传入参数有关
                if(vop == TV && pathvalueset.count(U)){
                    if(arg_origin_values.count(pop) == 1){
                        return true;
                    }
                    else
                        EV.push_back(pop);
                }
                continue;
            }

            LoadInst* LI = dyn_cast<LoadInst>(U);
            if(LI){
                EV.push_back(LI);
                continue;
            }

            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U);
            if(GEP){
                EV.push_back(GEP);
                continue;
            }

            PHINode *PN = dyn_cast<PHINode>(U);
            if(PN){
                EV.push_back(PN);
                continue;
            }
        }
    }

    return false;
}

bool PairAnalysisPass::checkValueRedefine(Function *F,
    Value *cirticalvalue,
    BasicBlock *CommonHead,
    EdgeIgnoreMap edgeIgnoreMap){

    if(!F || !cirticalvalue)
        return false;

    for(User *U : cirticalvalue->users()){
        if(U == cirticalvalue)
            continue;
        
        Instruction *I = dyn_cast<Instruction>(U);
        if(!I)
            continue;
        
        BasicBlock *U_BB = I->getParent();
        Instruction *U_TI = U_BB->getTerminator();
        if(!checkBlockPairConnectivity(U_BB,CommonHead,edgeIgnoreMap))
            continue;
        
        CallInst *CAI = dyn_cast<CallInst>(U);
        if(CAI){
            StringRef BB_FName = getCalledFuncName(CAI);
            if(BB_FName.empty())
                continue;

            if(Ctx->ReleaseFuncSet.count(BB_FName) || checkStringContainSubString(BB_FName,"free")){
                if(U_BB == CommonHead)
                    return true;

                for(BasicBlock *Succ : successors(U_TI)){
                    CFGEdge edge = make_pair(U_TI,Succ);
                    pair<CFGEdge,int> value(edge,1);
                    edgeIgnoreMap.insert(value);
                }       
            }
            continue;
        }
    }

    Instruction *Init = dyn_cast<Instruction>(cirticalvalue);
    if(Init!=NULL){
        BasicBlock *Init_BB = Init->getParent();
        if(!checkBlockPairConnectivity(Init_BB,CommonHead,edgeIgnoreMap)){
            return true;
        }
    }
    
    return false;
}