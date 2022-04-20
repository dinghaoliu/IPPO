#include <llvm/IR/Instructions.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Analysis/MemoryLocation.h>

#include "PointerAnalysis.h"
#include "Tools.h"

//#define TEST_ONE_CASE "__alloc_pbl"

/// Alias types used to do pointer analysis.
#define MUST_ALIAS

bool PointerAnalysisPass::doInitialization(Module *M) {
    return false;
}

bool PointerAnalysisPass::doFinalization(Module *M) {
    return false;
}

/// Detect aliased pointers in this function.
void PointerAnalysisPass::detectAliasPointers(Function *F,
    AAResults &AAR,
    PointerAnalysisMap &aliasPtrs) {
    
    std::set<AddrMemPair> addrSet; //pair<Value *, MemoryLocation *>
    Value *Addr1, *Addr2;
    MemoryLocation *MemLoc1, *MemLoc2;
    std::set<Value*> DstSet, LPSet;

    DstSet.clear();
    LPSet.clear();
    addrSet.clear();
    aliasPtrs.clear();

    // Scan instructions to extract all pointers.
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);

        LoadInst *LI = dyn_cast<LoadInst>(iInst);
        StoreInst *SI = dyn_cast<StoreInst>(iInst);
        CallBase *CB = dyn_cast<CallBase>(iInst);   //This line is changed

        if (LI) {
            MemLoc1 = new MemoryLocation();
            *MemLoc1 = MemoryLocation::get(LI);
            addrSet.insert(std::make_pair(LI->getPointerOperand(),
                                            MemLoc1));
            LPSet.insert(LI->getPointerOperand());
        } 
        else if (SI) {
            MemLoc1 = new MemoryLocation();
            *MemLoc1 = MemoryLocation::get(SI);
            addrSet.insert(std::make_pair(SI->getPointerOperand(),
                                            MemLoc1));
        } 
        else if (CB) {
            //ImmutableCallSite CS(CI);
            //CallBase CS(iInst);

            //Ignore debug functions
            StringRef FName = getCalledFuncName(CB);
            if (Ctx->DebugFuncs.count(FName) == 1)
                continue;
            if (FName.contains("err") || FName.contains("ERR"))
                continue;
            
            //OP<<"CB: "<<*CB<<"\n";

            //Consider pointer arguments 
            for (unsigned j = 0, ej = CB->getNumArgOperands();
                j < ej; ++j) {
                Value *Arg = CB->getArgOperand(j);

                if (!Arg->getType()->isPointerTy())
                    continue;

                MemLoc1 = new MemoryLocation();
                *MemLoc1 = MemoryLocation::getForArgument(CB, j, *TLI);
                addrSet.insert(std::make_pair(Arg, MemLoc1));

                Function *CF = CB->getCalledFunction();
                if (CF && CF->getName() == "copy_from_user" && j < 2)  
                    DstSet.insert(Arg);
            }
        }
    }

    for (std::set<AddrMemPair>::iterator it1 = addrSet.begin(),
        it1e = addrSet.end(); it1 != it1e; ++it1) {
        Addr1 = it1->first;
        MemLoc1 = it1->second;

        for (std::set<AddrMemPair>::iterator it2 = addrSet.begin(),
            it2e = addrSet.end(); it2 != it2e; ++it2) {
            if (it2 == it1)
                continue;

            Addr2 = it2->first;
            MemLoc2 = it2->second;

            if (Addr1 == Addr2)
                continue;

            //Compare different pointers
            AliasResult AResult = AAR.alias(*MemLoc1, *MemLoc2);
            if (AResult == MustAlias || AResult == PartialAlias) {
                OP <<"Addr1: "<<*Addr1<<"\n";
                OP <<"Addr2: "<<*Addr2<<"\n\n";
            }

#ifdef MUST_ALIAS
            if (AResult != MustAlias && AResult != PartialAlias) {
#else
		    if (AResult == NoAlias) {
#endif
                bool flag = true;

                if (AResult == MayAlias) {
                    CallInst *CI;

                    CI = dyn_cast<CallInst>(Addr1);
                    if (CI) {
                        StringRef FName = getCalledFuncName(CI);
                        if (FName.contains("kmalloc"))
                            flag = false;
                    }

                    CI = dyn_cast<CallInst>(Addr2);
                    if (CI) {
                        StringRef FName = getCalledFuncName(CI);
                        if (FName.contains("kmalloc"))
                            flag = false;
                    }

                    //Hack for copy_from_user - dst and SCheck
                    if (DstSet.find(Addr1) != DstSet.end() && 
                        LPSet.find(Addr2) != LPSet.end())
                            flag = false;
                    if (DstSet.find(Addr2) != DstSet.end() &&
                        LPSet.find(Addr1) != LPSet.end())
                            flag = false;
                    if (DstSet.find(Addr1) != DstSet.end() && 
                        DstSet.find(Addr2) !=  DstSet.end())
                            flag = false;
                }

                if (flag)
                    continue;
            }

            auto as = aliasPtrs.find(Addr1);
            if (as == aliasPtrs.end()) {
                std::set<Value *> sv;
                sv.clear();
                sv.insert(Addr2);
                aliasPtrs[Addr1] = sv;
            } else if (as->second.count(Addr2) == 0) {
                as->second.insert(Addr2);
            }
        }
    }
}


/// Detect aliased pointers in this function.
void PointerAnalysisPass::detectAliasPointers_new(Function *F,
    AAResults &AAR,
    PointerAnalysisMap &aliasPtrs,
    PointerAnalysisMap &structRelations) {

    set<Value*> ptrset;
    //set<PointerNode> ptrNodeSet;
    //list<PointerNode> ptrNodeList;
    //ptrNodeList.clear();
    map<Value*,set<Value *>> constraintSet;
    constraintSet.clear();

    // Scan instructions to extract all pointers.
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);

        IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(iInst);
        BitCastInst *BCI = dyn_cast<BitCastInst>(iInst);
		if (ITPI || BCI) {


        }

        CallInst *CAI = dyn_cast<CallInst>(iInst);
        if (CAI){
            StringRef FName = getCalledFuncName(CAI);

            //Ignore debug functions
            if (Ctx->DebugFuncs.count(FName) == 1)
                continue;
            if (FName.contains("err") || FName.contains("ERR"))
                continue;

            //Resolve data transfer functions
            if (FName.contains("_get_drvdata")) {
                Value *arg = CAI->getArgOperand(0);
                structRelations[arg].insert(CAI);
                ptrset.insert(CAI);
                //constraintSet[CAI].insert(CAI);

                continue;
            }
            if (FName.contains("_set_drvdata")) {
                Value *dev = CAI->getArgOperand(0);
                Value *data = CAI->getArgOperand(1);
                structRelations[dev].insert(data);
                ptrset.insert(CAI);
                continue;
            }
            if (FName.contains("copy_from_user") || FName.contains("copy_to_user")) {
                Value *dst = CAI->getArgOperand(0);
                Value *source = CAI->getArgOperand(1);
                aliasPtrs[dst].insert(source);
                aliasPtrs[source].insert(dst);
                continue;
            }
        }

        LoadInst* LI = dyn_cast<LoadInst>(iInst);
        if (LI) {
            if (!LI->getType()->isPointerTy())
                continue;
            
            Value *LPO = LI->getPointerOperand();
        }

        StoreInst *SI = dyn_cast<StoreInst>(iInst);
        if(SI){

        }

        if (!iInst->getType()->isPointerTy())
            continue;
        
        ptrset.insert(iInst);
    }

    for (auto it1 = ptrset.begin(); it1 != ptrset.end(); it1++) {
        Value* v1 = *it1;
        
        for (auto it2 = ptrset.begin(); it2 !=ptrset.end();it2++){
            Value* v2 = *it2;

            if (v1 == v2)
                continue;

            AliasResult AResult = AAR.alias(v1, v2);
            if (AResult == MustAlias || AResult == PartialAlias ){ //|| AResult == MayAlias
                OP <<"v1: "<<*v1<<"\n";
                OP <<"v2: "<<*v2<<"\n\n";
            }
        }
    }
}

void PointerAnalysisPass::detectStructRelation(Function *F,
    PointerAnalysisMap &structRelations){
    
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);

        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(iInst);
        if(GEP){
            if (!GEP->getType()->isPointerTy())
                continue;
            
            
            Value *PO = GEP->getPointerOperand();
            structRelations[PO].insert(GEP);

            std::set<Value *> PV; //Global value set to avoid loop
            std::list<Value *> EV; //BFS record list
            PV.clear();
            EV.clear();

            //Collect member's users
            for(User *U :GEP->users()){
                EV.push_back(U);
            }

            while (!EV.empty()) {

                Value *TV = EV.front(); //Current checking value
                EV.pop_front();

                if (PV.find(TV) != PV.end())
                    continue;
                PV.insert(TV);

                //OP << "TV: "<<*TV<<"\n";
  
                BitCastInst *BCI = dyn_cast<BitCastInst>(TV);
                LoadInst* LI = dyn_cast<LoadInst>(TV);

                if(BCI || LI){
                    if(!TV->getType()->isPointerTy())
                        continue;

                    structRelations[PO].insert(TV);
                    Value *op;
                    
                    if(BCI) {
                        op = BCI->getOperand(0);
                    }
                    else
                        op = LI->getOperand(0);
                    structRelations[PO].insert(op);
                    EV.push_back(op);

                    for(User *u : TV->users()){
                        if(u == TV)
                            continue;
                        EV.push_back(u);
                    }
                    continue;
                }

                PHINode *PN = dyn_cast<PHINode>(TV);
                if(PN){
                    if(!TV->getType()->isPointerTy())
                        continue;
                    structRelations[PO].insert(PN);

                    for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                        Value *IV = PN->getIncomingValue(i);
                        structRelations[PO].insert(IV);
                        EV.push_back(IV);
                    }

                    for(User *u : TV->users()){
                        if(u == TV)
                            continue;
                        EV.push_back(u);
                    }

                    continue;
                }

                SelectInst *SI = dyn_cast<SelectInst>(TV);


                StoreInst *STI = dyn_cast<StoreInst>(TV);
                if(STI){
                    Value* vop = STI->getValueOperand();
                    Value* pop = STI->getPointerOperand();

                    //if(pop == GEP && vop->getType()->isPointerTy()){
                    if(structRelations[PO].count(pop) && vop->getType()->isPointerTy()){
                        structRelations[PO].insert(vop);
                        EV.push_back(vop);
                    }
                            
                    //if(vop == GEP && pop->getType()->isPointerTy()){
                    if(structRelations[PO].count(vop) && pop->getType()->isPointerTy()){
                        structRelations[PO].insert(pop);
                        EV.push_back(pop);
                    }
                }

            }

        }
    }

    //We have resolved getelementptr instructions
    //Then we check load & store
    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);
    
        LoadInst* LI = dyn_cast<LoadInst>(iInst);
        BitCastInst *BCI = dyn_cast<BitCastInst>(iInst);

        if((LI || BCI) && iInst->getType()->isPointerTy()) {

            auto op = iInst->getOperand(0);

            if(structRelations.count(iInst)){
                structRelations[op].insert(structRelations[iInst].begin(), structRelations[iInst].end());
            }

            if(structRelations.count(op)){
                structRelations[iInst].insert(structRelations[op].begin(), structRelations[op].end());
            }
        }
    }


}

void PointerAnalysisPass::detectStructRelation_new(Function *F,
    PointerAnalysisMap &structRelations){

    map<Value*,StructNode*> globalrecord;

    for (inst_iterator i = inst_begin(F), ei = inst_end(F); i != ei; ++i) {
        Instruction *iInst = dyn_cast<Instruction>(&*i);

        //OP << "Inst: "<<*iInst<<"\n";

        //Build node for every llvm value
        StructNode *stnode;
        if(globalrecord.count(iInst) != 0) {
            stnode = globalrecord[iInst];
        }
        else {
            stnode = new StructNode();
            globalrecord[iInst] = stnode;
        }

        stnode->insert_member(iInst);

        BitCastInst *BCI = dyn_cast<BitCastInst>(iInst);
        LoadInst* LI = dyn_cast<LoadInst>(iInst);
        IntToPtrInst *ITPI = dyn_cast<IntToPtrInst>(iInst);
        PtrToIntInst *PTII = dyn_cast<PtrToIntInst>(iInst);
        if(BCI || LI || ITPI || PTII){
            
            Value *op;
            if(BCI) 
                op = BCI->getOperand(0);
            else if(LI)
                op = LI->getOperand(0);
            else if(ITPI)
                op = ITPI->getOperand(0);
            else 
                op = PTII->getOperand(0);
            
            //Merge current node with op
            if(globalrecord.count(op)!=0){
                StructNode *opnode = globalrecord[op];
                opnode->mergeNode(*stnode);
                globalrecord[iInst] = opnode;
            }
            else {
                stnode->insert_member(op);
                globalrecord[op] = stnode;
            }

            continue;
        }


        PHINode *PN = dyn_cast<PHINode>(iInst);
        if(PN){
            
            if(!iInst->getType()->isPointerTy())
                continue;
            
            for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                Value *IV = PN->getIncomingValue(i);

                if(isConstant(IV))
                    continue;

                if(globalrecord.count(IV)!=0){
                    StructNode* IVnode = globalrecord[IV];
                    stnode->mergeNode(*IVnode);
                }
                else {
                    stnode->insert_member(IV);
                }
            }

            for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i){
                Value *IV = PN->getIncomingValue(i);
                if(isConstant(IV))
                    continue;
                globalrecord[IV] = stnode;
            }

            continue;
        }

        SelectInst *SI = dyn_cast<SelectInst>(iInst);
        if(SI){

            auto TV = SI->getTrueValue();
            auto FV = SI->getFalseValue();

            if(globalrecord.count(TV)!=0){
                StructNode* TVNode = globalrecord[TV];
                stnode->mergeNode(*TVNode);
            }
            else {
                stnode->insert_member(TV);
            }

            if(globalrecord.count(FV)!=0){
                StructNode* FVNode = globalrecord[FV];
                stnode->mergeNode(*FVNode);
            }
            else{
                stnode->insert_member(FV);
            }

            globalrecord[TV] = stnode;
            globalrecord[FV] = stnode;

            continue;
        }

        StoreInst *STI = dyn_cast<StoreInst>(iInst);
        if(STI){

            //Store vop in pop
            Value* vop = STI->getValueOperand();
            Value* pop = STI->getPointerOperand();

            if(isConstant(vop))
                continue;

            StructNode* popNode = new StructNode();
            if(globalrecord.count(pop)!=0){
                popNode = globalrecord[pop];
            }
            else {
                popNode->insert_member(pop);
            }

            StructNode* vopNode = new StructNode();
            if(globalrecord.count(vop)!= 0){
                vopNode = globalrecord[vop];
            }
            else {
                vopNode->insert_member(vop);
            }
            
            popNode->mergeNode(*vopNode);

            globalrecord[vop] = popNode;
            continue;
        }

        GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(iInst);
        if(GEP){
            if (!GEP->getType()->isPointerTy())
                continue;

            Value *ParrentValue = GEP->getPointerOperand();

            StructNode* pnode = new StructNode();
            if(globalrecord.count(ParrentValue) != 0)
                pnode = globalrecord[ParrentValue];
            else {
                pnode->insert_member(ParrentValue);
                globalrecord[ParrentValue] = pnode;
            }
            
            //pnode->MemberSet.insert(GEP);
            pnode->MemberNodeSet.insert(stnode);

            continue;
        }
    }

    for(auto it = globalrecord.begin(); it != globalrecord.end();it++){
        StructNode* node = it->second;

        if(!node->MemberNodeSet.empty()){
            for(auto i = node->MemberNodeSet.begin(); i!=node->MemberNodeSet.end();i++){
                StructNode* member = *i;
                node->MemberValueSet.insert(member->NodeSet.begin(),member->NodeSet.end());
            }   
        }
    }

    for(auto it = globalrecord.begin(); it != globalrecord.end();it++){
        StructNode* node = it->second;

        if(!node->MemberNodeSet.empty()){
            for(auto i = node->MemberNodeSet.begin(); i!=node->MemberNodeSet.end();i++){
                StructNode* member = *i;
                node->MemberValueSet.insert(member->MemberValueSet.begin(),member->MemberValueSet.end());
            }   
        }
    }

    for(auto it = globalrecord.begin(); it != globalrecord.end();it++){
        Value *v = it->first;
        StructNode* node = it->second;
    
        structRelations[v].insert(node->MemberValueSet.begin(), node->MemberValueSet.end());
    
    }
}

bool PointerAnalysisPass::doModulePass(Module *M) {
    // Save TargetLibraryInfo.

    Triple ModuleTriple(M->getTargetTriple());
    TargetLibraryInfoImpl TLII(ModuleTriple);
    TLI = new TargetLibraryInfo(TLII);

    // Run BasicAliasAnalysis pass on each function in this module.
    // XXX: more complicated alias analyses may be required.
    legacy::FunctionPassManager *FPasses = new legacy::FunctionPassManager(M);
    AAResultsWrapperPass *AARPass = new AAResultsWrapperPass();

    FPasses->add(AARPass);

    FPasses->doInitialization();
    for (Function &F : *M) {
        if (F.isDeclaration())
            continue;

        FPasses->run(F);
    }
    FPasses->doFinalization();

    // Basic alias analysis result.
    AAResults &AAR = AARPass->getAAResults();

    for (Module::iterator f = M->begin(), fe = M->end();
        f != fe; ++f) {
        Function *F = &*f;
        PointerAnalysisMap aliasPtrs; //map<llvm::Value *, std::set<llvm::Value *>>
        PointerAnalysisMap structRelations;

#ifdef TEST_ONE_CASE
        if (F->getName()!= TEST_ONE_CASE)
            continue;
#endif

        if (F->empty())
            continue;
        
        // Only consider security operation related functions
        //if (Ctx->SecurityOperationSets.count(F) == 0)
        //    continue;

        //detectAliasPointers(F, AAR, aliasPtrs);
        //detectAliasPointers_new(F, AAR, aliasPtrs, structRelations);
        //detectStructRelation(F, structRelations);
        detectStructRelation_new(F, structRelations);

        // Save pointer analysis result.
        Ctx->FuncPAResults[F] = aliasPtrs;
        Ctx->FuncAAResults[F] = &AAR;

        Ctx->FuncStructResults[F] = structRelations;
    }

    return false;
}
