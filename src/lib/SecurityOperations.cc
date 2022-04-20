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
#include <regex>
#include <algorithm>
#include <unistd.h>

#include "SecurityOperations.h"
#include "Config.h"
#include "Common.h"

using namespace llvm;
using namespace std;

//#define TEST_ONE_CASE ""
//#define PRINT_RESOURCE_RELATED_OPERATION 1
//#define PRINT_Init_OPERATION
//#define PRINT_LOCK_UNLOCK_OPERATION 1

bool SecurityOperationsPass::updateConnectGraph(ConnectGraph &connectGraph,
    vector<BasicBlock*> globalblockset){

    bool changetag = false;

    if(connectGraph.empty())
        return changetag;
    
    for(auto rit = connectGraph.rbegin(); rit != connectGraph.rend();rit++){
        Blockpair blockpair = rit->first;
        BasicBlock* firstbb = blockpair.first;
        BasicBlock* secondbb = blockpair.second;
        if(rit->second && firstbb != secondbb){
            
            for(auto it = globalblockset.begin(); it != globalblockset.end();it++){
                //Blockpair blockpair_in = it->first;
                BasicBlock* firstbb_in = *it;
                //BasicBlock* secondbb_in = blockpair_in.second;
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
void SecurityOperationsPass::initConnectGraph(Function *F,ConnectGraph &connectGraph,
    vector<BasicBlock*> globalblockset,
    EdgeIgnoreMap edgeIgnoreMap){

    connectGraph.clear();
    if(!F)
        return;

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
            if(edgeIgnoreMap.count(edge)!=0){
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

void SecurityOperationsPass::identifyRefcountFuncs(Function *F,
    set<SecurityOperation *> &SecurityOperationSet){
    
    if(!F)
        return;
    
    for(inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i){

        Instruction *Inst = &*i;

        CallInst *CAI = dyn_cast<CallInst>(&*i);
        if(CAI){
            Function *CF = CAI->getCalledFunction();
			if (!CF){
                continue;
            }

            StringRef FName = getCalledFuncName(CAI);
        
            if(1 == Ctx->RefcountFuncs.count(FName)){

                unsigned argnum = CAI->getNumArgOperands();

                if(argnum == 0){
                    //SecurityOperation SO(PairFunc,&*i,NULL);
                    SecurityOperationSet.insert(new SecurityOperation(RefcountOperation,&*i,NULL));
                }

                for(unsigned j=0;j<argnum;j++){
                    Value* arg = CAI->getArgOperand(j);

                    //SecurityOperation SO(PairFunc,&*i,arg);
                    SecurityOperationSet.insert(new SecurityOperation(RefcountOperation,&*i,arg));
                }
                continue;
            }
        }
    }
}

Value * SecurityOperationsPass::findlastuse(Function *F, Value *V){
    
    if(!F || !V)
        return V;
    
    Value *lastuse = V;
    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
	EV.push_back(V);

    while (!EV.empty()) {

        Value *TV = EV.front(); //Current checking value
        lastuse = TV;
		EV.pop_front();

        if (PV.find(TV) != PV.end())
			continue;

		PV.insert(TV);
        Instruction *I = dyn_cast<Instruction>(TV);
        if(!I)
            continue;
        
        ///////////////////////////////////////////////
        // The value (%TV) is a load: %TV = load i32, i32* %LPO
        ///////////////////////////////////////////////
        LoadInst* LI = dyn_cast<LoadInst>(TV);
        if(LI){

            auto numuse = LI->getNumUses();
            if(numuse != 0){
                auto lastuse_LI = LI->user_back();
                EV.push_back(lastuse_LI);
            }
            continue;
        }

        auto opcodeName = I->getOpcodeName();
        ///////////////////////////////////////////////
        // The value is a single operation instruction.
        ///////////////////////////////////////////////
        if(1 == Ctx->SingleOperandInsts.count(opcodeName)){
            
            auto numuse = TV->getNumUses();

            if(numuse != 0){
                auto lastuse_singleoperand = TV->user_back();
                //OP << "lastuse_LI: "<<*lastuse_LI<<"\n";
                EV.push_back(lastuse_singleoperand);
            }

            continue;
        }
    }

    return lastuse;
}

bool SecurityOperationsPass::checkvaliduse(Value *V){
    if(!V)
        return false;
    
    //The release function is expected to have no return value
    Type * UTy= V->getType();
    if(!UTy->isVoidTy()){
        return false;
    }

    CallInst *isCAI = dyn_cast<CallInst>(V);
    if(!isCAI)
        return false;
    else{
        unsigned argnum = isCAI->getNumArgOperands();

        StringRef calledFName = getCalledFuncName(isCAI);
        if(calledFName.contains("err"))
            return false;

        if(!calledFName.contains("free")){
            if(!calledFName.contains("release"))
                return false;
        }

        Value* arg = isCAI->getArgOperand(0);
        Type *argTy = arg->getType();
        if(!argTy->isPointerTy())
            return false;
    }

    return true;
}

void SecurityOperationsPass::identifyResourceAcquisition(Function *F,
    set<SecurityOperation *> &SecurityOperationSet){

    if(!F)
        return;
    
    set<Value *>F_argset;
    F_argset.clear();
    for(auto it = F->arg_begin(); it != F->arg_end();it++){
        F_argset.insert(it);
    }

    vector<BasicBlock*> globalblockset;
    initGlobalBlockSet(F,globalblockset);
    ConnectGraph connectGraph;
    EdgeIgnoreMap edgeIgnoreMap;
    edgeIgnoreMap.clear();
    initConnectGraph(F,connectGraph, globalblockset, edgeIgnoreMap);


    for(inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i){

        Instruction *Inst = &*i;
        CallInst *CAI = dyn_cast<CallInst>(&*i);
		if(CAI){
            Function *CF = CAI->getCalledFunction();
            Type * Ty= CAI->getType();
            if(!Ty)
                continue;
            
            //Ignore llvm debug functions
            StringRef FName = getCalledFuncName(CAI);
            if(Ctx->DebugFuncs.count(FName) == 1)
                continue;
            if(Ctx->AutoFreedFuncs.count(FName) == 1)
                continue;
            
            //Ignore functions with a const string parameter
            auto have_const_string = false;
            unsigned argnum = CAI->getNumArgOperands();
            for(unsigned j=0;j<argnum;j++){
                Value* arg = CAI->getArgOperand(j);
                if(!isa<ConstantExpr>(arg))
                    continue;

                auto ptr = dyn_cast<ConstantExpr>(arg);
                if(ptr){
                    //OP <<"Found const string\n";
                    have_const_string = true;
                        break;
                }
            }

            //An optional setting
            if(have_const_string){
                //resource_acq_value = Inst;
                //resource_acq_value_set.insert(Inst);
                //continue;
            }

            set<Value *> resource_acq_value_set;
            resource_acq_value_set.clear();

            //The function call returns a pointer
            if(Ty->isPointerTy()){
                resource_acq_value_set.insert(Inst);
            }

            //The return value is a pointer, then this pointer is a resource acquisition
            //Otherwise, the value need to be a address taken parameter of a function
			if (!Ty->isPointerTy()){

                //Currently ignore this case
                continue;
                //OP << "Return value is not a pointer\n";
                unsigned argnum = CAI->getNumArgOperands();
                for(unsigned j=0;j<argnum;j++){
                    Value* arg = CAI->getArgOperand(j);
                    Type * argTy= arg->getType();

                    //This case need to be resolved specifically
                    AllocaInst *AI = dyn_cast<AllocaInst>(arg);
                    if(AI){
                        argTy = AI->getAllocatedType();
                        continue;
                    }

                    //The parameter needs to be a pointer, too
                    if(!argTy->isPointerTy()){
                        //OP << "Not a pointer param: "<<*arg<<"\n";
                        continue;
                    }

                    //Currently we ignore the paramters of F
                    if(F_argset.count(arg) == 1)
                        continue;

                    //auto att = CAI->getParamAttr(argnum, llvm::Attribute::AttrKind::None);
                    auto nonnull_attr = CAI->getParamAttr(j, Attribute::NonNull);
                    
                    string str = nonnull_attr.getAsString();
                    if(str.length()!=0){

                        //Check from the source file: must contain '&'
                        string CAI_sourcecode = getSourceLine(CAI);
                        if(!checkStringContainSubString(CAI_sourcecode,"&")){
                            continue;
                        }
                        if(checkStringContainSubString(CAI_sourcecode,"&&")){
                            continue;
                        }
                        resource_acq_value_set.insert(arg);
                    }
                }
            }

            //Find the last use of the resource
            if(!resource_acq_value_set.empty()){
                for(auto it = resource_acq_value_set.begin(); it != resource_acq_value_set.end();it++){
                    Value *resource_acq_value = *it;
                    auto numuse = resource_acq_value->getNumUses();

                    //这里应该用连通关系来界定lastuse
                    if(numuse != 0){

                        Value * lastuse = NULL;
                        set<Value *> validuserset;
                        validuserset.clear();
                        set<Value *> invaliduserset;
                        invaliduserset.clear();

                        std::set<Value *> PV; //Global value set to avoid loop
                        std::list<Value *> EV; //BFS record list
                        PV.clear();
                        EV.clear();
                        EV.push_back(resource_acq_value);
                        while (!EV.empty()) {

                            Value *TV = EV.front(); //Current checking value
                            EV.pop_front();

                            if (PV.find(TV) != PV.end())
                                continue;
                            PV.insert(TV);


                            for(User *U :TV->users()){
                                if(U == resource_acq_value)
                                    continue;
                                
                                BitCastInst *BCI = dyn_cast<BitCastInst>(U);
                                if(BCI){
                                    EV.push_back(BCI);
                                    if(invaliduserset.count(TV)){
                                        invaliduserset.insert(U);
                                    }
                                    continue;
                                }

                                StoreInst *STI = dyn_cast<StoreInst>(U);
                                if(STI){
                                    Value* pop = STI->getPointerOperand();
                                    
                                    EV.push_back(pop);
                                    if(invaliduserset.count(TV)){
                                        invaliduserset.insert(U);
                                    }
                                    continue;
                                }

                                LoadInst* LI = dyn_cast<LoadInst>(U);
                                if(LI){
                                    EV.push_back(LI);
                                    if(invaliduserset.count(TV))
                                        invaliduserset.insert(U);
                                    continue;
                                }

                                GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U);
                                if(GEP){
                                    EV.push_back(GEP);
                                    invaliduserset.insert(GEP);
                                    continue;
                                }

                                PHINode *PN = dyn_cast<PHINode>(U);
                                if(PN){
                                    EV.push_back(PN);
                                    if(invaliduserset.count(TV))
                                        invaliduserset.insert(U);
                                    continue;
                                }

                                ReturnInst *RI = dyn_cast<ReturnInst>(U);
                                if(RI){
                                    continue;
                                }

                                validuserset.insert(U);

                                if(invaliduserset.count(TV))
                                    invaliduserset.insert(U);
                            }
                        }
                        
                        if(validuserset.empty())
                            continue;

                        set<Value *> checkedlastuseset;
                        checkedlastuseset.clear();
                        if(validuserset.size()>1){
                            lastuse = NULL;

                            //There could be more than one valid user
                            for(auto it = validuserset.begin(); it != validuserset.end();it++){

                                Instruction *currentuse = dyn_cast<Instruction>(*it);
                                if(!currentuse)
                                    continue;

                                BasicBlock* currentuseblock = currentuse->getParent();
                                bool findtag = true;

                                for(auto j = validuserset.begin(); j != validuserset.end();j++){

                                    Instruction *otheruse = dyn_cast<Instruction>(*j);
                                    if(!otheruse)
                                        continue;
                                    
                                    //Igonre currentuse itself
                                    if(otheruse == currentuse)
                                        continue;

                                    BasicBlock* otheruseblock = otheruse->getParent();

                                    //检测同一个block内的先后关系
                                    if(otheruseblock == currentuseblock){
                                        DominatorTree DT = DominatorTree();
                                        DT.recalculate(*F);
                                        if(DT.dominates(currentuse,otheruse)){
                                            findtag = false;
                                            break;
                                        }
                                    }
                                    else{
                                        //Current use is not the last use
                                        Blockpair blockpair(currentuseblock,otheruseblock);
                                        if(connectGraph[blockpair]){
                                            findtag = false;
                                            break;
                                        }
                                    }
                                }

                                //current use cannot reach any other use, this is the last use
                                if(findtag){
                                    lastuse = *it;
                                    if(invaliduserset.count(lastuse)) {
                                        continue;
                                    }
                                    //OP <<"Here\n";
                                    if(checkvaliduse(lastuse)){
                                        //Found a valid last use
                                        if(lastuse == NULL || lastuse == CAI || lastuse == resource_acq_value)
                                            continue;

                                        BasicBlock* caiblock = CAI->getParent();
                                        Instruction *useinst = dyn_cast<Instruction>(lastuse);
                                        BasicBlock* useblock = useinst->getParent();
                                        Blockpair blockpair(useblock,caiblock);
                                        if(connectGraph[blockpair]){
                                            continue;
                                        }

                                        checkedlastuseset.insert(lastuse);
                                    }
                                    else
                                        lastuse = NULL;
                                }
                            }
                        }
                        else{
                            lastuse = *(validuserset.begin());
                            if(invaliduserset.count(lastuse))
                                continue;
                            if(!checkvaliduse(lastuse)){
                                lastuse = NULL;
                            }
                            else{
                                checkedlastuseset.insert(lastuse);
                            }
                        }

                        if(checkedlastuseset.empty())
                            continue;

                        //Use predefined list to correct lead-follow functions
                        for(auto it = checkedlastuseset.begin(); it != checkedlastuseset.end(); ++it){
                            CallInst *freeCAI = dyn_cast<CallInst>(*it);
                            StringRef freeFName = getCalledFuncName(freeCAI);
                            if(Ctx->PairFuncs.count(freeFName) == 1){
                                for(inst_iterator it = inst_begin(F), eit = inst_end(F); it != eit; ++it){
                                    Instruction *Inst = &*it;
                                    CallInst *CAI = dyn_cast<CallInst>(Inst);
                                    if(CAI){
                                        StringRef funcname = getCalledFuncName(CAI);
                                        
                                        if(Ctx->PairFuncs[freeFName].count(funcname) == 1){
                                            SecurityOperationSet.insert(new SecurityOperation(ResourceAcquisition,CAI,resource_acq_value));
                                            SecurityOperationSet.insert(new SecurityOperation(ResourceRelease,freeCAI,resource_acq_value));
                                            #ifdef PRINT_RESOURCE_RELATED_OPERATION
                                            OP << "Resource: "<< *CAI <<"\n";
                                            OP << "Alloc: "<< *CAI <<"\n";
                                            OP << "Release: "<< *freeCAI <<"\n\n";
                                            #endif
                                        }
                                    }
                                }
                                continue;
                            }
                        }

                        SecurityOperationSet.insert(new SecurityOperation(ResourceAcquisition,&*i,resource_acq_value));
#ifdef PRINT_RESOURCE_RELATED_OPERATION
                        OP << "resource_acq_value: "<< *resource_acq_value <<"\n";
#endif
                        for(auto it = checkedlastuseset.begin(); it != checkedlastuseset.end(); ++it){
#ifdef PRINT_RESOURCE_RELATED_OPERATION
                            OP<<"Valid use: "<< *(*it)<<"\n";
#endif
                            SecurityOperationSet.insert(new SecurityOperation(ResourceRelease,*it,resource_acq_value));
                        }
                    }
                }
            }
        }
    }
}


void SecurityOperationsPass::identifyInitialization(Function *F, 
    set<SecurityOperation *> &SecurityOperationSet){
    
    if(!F)
        return;
    
    set<Value *>argset;
    argset.clear();
    for(auto it = F->arg_begin(); it != F->arg_end();it++){
        argset.insert(it);
    }

    //Record initedvar - init operations
    map<Value*,set<Value *>> initMap;
    initMap.clear();

    DominatorTree DT = DominatorTree();
    DT.recalculate(*F);

    for(inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i){

        Instruction *Inst = &*i;
    
        ///////////////////////////////////////////////
        // The value is a store instruction. store i32 vop, i32* pop (store vop in pop)
        ///////////////////////////////////////////////
        StoreInst *STI = dyn_cast<StoreInst>(Inst);
        if(STI){
            
            //Currently ignore such kind of initialization.
            continue;

            Value* vop = STI->getValueOperand();
            Value* pop = STI->getPointerOperand();

            Type *vopType = vop->getType();

            //Global variables need not to init, so ignore them
            auto globalvar = dyn_cast<GlobalValue>(pop);
            if(globalvar){
                continue;
            }

            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(pop);
            if(GEP){
                //OP << "GEP: "<<*GEP <<"\n";
                Value* op0 = GEP->getPointerOperand();
                //OP << "OP0: "<<*op0 <<"\n";
                auto user_op0 = dyn_cast<User>(op0);
                if(user_op0 && user_op0->getNumOperands() > 0){
                    auto op00 = user_op0->getOperand(0);
                    
                    if(argset.count(op00) != 0){
                        continue;
                    }
                    if(op00){
                        //OP << "op00: "<<*op00 <<"\n";
                        auto globalvar = dyn_cast<GlobalValue>(op00);
                        if(globalvar){
                            //OP<<"is global\n";
                            continue;
                        }
                    }
                }
               
            }

            //if(isConstant(vop) && !isConstant(pop)){
            if(vopType->isIntegerTy() || vopType->isPointerTy() ){

                auto user_op0 = dyn_cast<User>(pop);
                if(user_op0 && user_op0->getNumOperands() > 0){
                    //OP<<"True\n";
                    auto op00 = user_op0->getOperand(0);
                    if(op00){
                        if(argset.count(op00) != 0){
                            continue;
                        }
                        //OP<<"op00: "<< *op00 <<"\n";
                        auto globalvar = dyn_cast<GlobalValue>(op00);
                        if(globalvar){
                            continue;
                        }
                    }
                }

                //Ignore arguments
                if(argset.count(pop) != 0){
                    continue;
                }

                bool validinit = true;

                //Check if current init is the first init
                //We only record the first init for a given inited var
                if(initMap.count(pop) == 1){
                    set<Value *> initoperations = initMap[pop];
                    for(auto it = initoperations.begin(); it != initoperations.end();){
                        Value *initoperation = *it;
                        auto *I_init = dyn_cast<Instruction>(initoperation);
                        //BasicBlock *I_init_bb = I_init->getParent();
                        //BasicBlock *I_init_current_bb = Inst->getParent();

                        if(DT.dominates(I_init,Inst)){
                            validinit = false;
                            break;
                        }

                        if(DT.dominates(Inst,I_init)){
                            initoperations.erase(it++);
                        }
                        else{
                            it++;
                        }
                    }
                }

                if(validinit){
                    SecurityOperationSet.insert(new SecurityOperation(Initialization,&*i,pop));
                    initMap[pop].insert(&*i);
                    #ifdef PRINT_Init_OPERATION
                    OP << "init: "<< *Inst <<"\n";
                    OP << "CV: "<< *pop <<"\n";
                    Type * UTy= pop->getType();
                    OP << "CV type: "<<*UTy <<"\n\n"; //maybe struct type
                    //OP << "CV name: "<<pop->hasName()<<"\n";
                    #endif
                }
            }
            continue;
        }
        
        CallInst *CAI = dyn_cast<CallInst>(&*i);
        if(CAI){

            ///////////////////////////////////////////////
            // The value is a memset call
            ///////////////////////////////////////////////
            StringRef FName = getCalledFuncName(CAI);
            if(FName == "llvm.memset.p0i8.i64" || FName == "llvm.memset.p0i8.i32"
                || FName == "__memset"){
                Value * criticalvar = CAI->getArgOperand(0);
                Value * fillvar = CAI->getArgOperand(1);
                if(isConstant(fillvar)){
                    //auto fillvar_const = dyn_cast<Constant>(fillvar);
                    //if(fillvar_const->isNullValue()){
                    SecurityOperationSet.insert(new SecurityOperation(Initialization,&*i,criticalvar));
                    #ifdef PRINT_Init_OPERATION
                    OP << "init: "<< *Inst <<"\n";
                    OP << "CV: "<< *criticalvar <<"\n";
                    #endif
                    continue;
                    //}
                }
            }

            ///////////////////////////////////////////////
            // The value is a memcpy call
            ///////////////////////////////////////////////
            if(FName == "llvm.memcpy.p0i8.i64" || FName == "llvm.memcpy.p0i8.i32"
                || FName == "__memcpy"){
                Value * criticalvar = CAI->getArgOperand(0);
                SecurityOperationSet.insert(new SecurityOperation(Initialization_memcpy,&*i,criticalvar));
                continue;
            }
        }
    }
}

//Find lock & unlock function
//Todo: need to further improve this algorithm
void SecurityOperationsPass::identifyLockUnlock(Function *F, 
    set<SecurityOperation *> &SecurityOperationSet){

    if(!F)
        return;
    
    if(F->getName().contains("lock"))
        return;

    for(inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i){

        Instruction *Inst = &*i;

        CallInst *CAI = dyn_cast<CallInst>(&*i);
        if(CAI){
            StringRef FName = getCalledFuncName(CAI);

            //Find lock function
            if(FName.contains("_lock") || FName.contains("_trylock") || FName.contains("_spinlock")){
                
                Value * criticalvar_lock;
                unsigned argnum = CAI->getNumArgOperands();
                if(argnum == 0){
                    criticalvar_lock = NULL;
                }
                else{
                    criticalvar_lock = CAI->getArgOperand(0);
                    CallInst *CAI_arg = dyn_cast<CallInst>(criticalvar_lock);
                    if(CAI_arg && CAI_arg->getNumOperands()!=0){
                        StringRef arg_FName = getCalledFuncName(CAI_arg);
                        if(arg_FName.contains("lock"))
                            criticalvar_lock = CAI_arg->getOperand(0);
                    }
                }

                SecurityOperationSet.insert(new SecurityOperation(Lock,&*i,criticalvar_lock));
                #ifdef PRINT_LOCK_UNLOCK_OPERATION
                OP<<"Lock: "<<*CAI <<"\n";
                if(criticalvar_lock == NULL) 
                    OP<<"--target_var: NULL \n";
                else
                    OP<<"--target_var: "<<*criticalvar_lock <<"\n";
                #endif
            }

            //Find unlock function
            if(FName.contains("_unlock")){

                //Ignore "_unlocked" function
                if(FName.contains("_unlocked"))
                    continue;
                
                Type * Ty= CAI->getType();
                if(!Ty)
                    continue;
                if(!Ty->isVoidTy())
                    continue;

                Value * criticalvar_unlock;
                unsigned argnum = CAI->getNumArgOperands();
                if(argnum == 0){
                    criticalvar_unlock = NULL;
                }
                else
                    criticalvar_unlock = CAI->getArgOperand(0);

                SecurityOperationSet.insert(new SecurityOperation(Unlock,&*i,criticalvar_unlock));
                #ifdef PRINT_LOCK_UNLOCK_OPERATION
                    OP<<"Unlock: "<<*CAI <<"\n";
                if(criticalvar_unlock == NULL)
                    OP<<"--target_var: NULL \n";
                else
                    OP<<"--target_var: "<<*criticalvar_unlock <<"\n";
                #endif
            }
        }
    }
}


void SecurityOperationsPass::identifySecurityOperations(Function *F){

    if(!F)
        return;
    
    set<SecurityOperation *> SecurityOperationSet;
    SecurityOperationSet.clear();

    //Identify Security Operations
    identifyRefcountFuncs(F,SecurityOperationSet);

    identifyResourceAcquisition(F,SecurityOperationSet);

    //This function is under test
    //identifyInitialization(F,SecurityOperationSet);

    //This function is under test
    identifyLockUnlock(F,SecurityOperationSet);

    ///Todo: add other security operations

    if(SecurityOperationSet.empty())
        return;

    //Update global counter
    for(auto it = SecurityOperationSet.begin(); it != SecurityOperationSet.end();it++){

        SecurityOperation *SO = *it;
        switch(SO->operationType){
            case ResourceAcquisition:
                Ctx->NumResourceAcq += 1;
                break;
            case ResourceRelease:
                Ctx->NumReleaseFucs += 1;
                break;
            case RefcountOperation:
                Ctx->NumRefcountFuncs += 1;
                break;
            case Unlock:
                Ctx->NumLockRelatedFucs +=1;
                break;
        }
    }

    for (auto SO : SecurityOperationSet) {
		Ctx->SecurityOperationSets[F].insert(*SO);
	}
}

bool SecurityOperationsPass::doInitialization(Module *M) {
  return false;
}

bool SecurityOperationsPass::doFinalization(Module *M) {
  return false;
}

bool SecurityOperationsPass::doModulePass(Module *M) {
    
    //Find security operations for each function
	for(Module::iterator f = M->begin(), fe = M->end();
			f != fe; ++f) {
		Function *F = &*f;

		if (F->empty())
			continue;

		if (F->size() > MAX_BLOCKS_SUPPORT)
			continue;

        //Test for one function
#ifdef TEST_ONE_CASE
        if(F->getName()!= TEST_ONE_CASE)
            continue;
#endif

        //F is not empty
        Ctx->NumFunctions++;

        identifySecurityOperations(F);
	}

	return false;
}