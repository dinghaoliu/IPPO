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

#include "WrapperAnalysis.h"
#include "Config.h"
#include "Common.h"

using namespace llvm;
using namespace std;

//#define TEST_ONE_CASE "vc4_validate_shader"

void WrapperAnalysisPass::findAllValidCallers(
    Function *F, 
    CallInst *CAI, 
    set<Function *> &validcallers){
    if(!F)
        return;
    
    std::list<Function *> EF; //BFS record list
    std::set<Function *> PF; //Global value set to avoid loop
    EF.clear();
    PF.clear();
    
    CallInstSet callers = Ctx->Callers[F];
    for(auto it = callers.begin(); it != callers.end();it++){
        CallInst *caller = *it;
        Function *f = caller->getFunction();
        if(Ctx->ReleaseFuncSet.count(f->getName()) == 1)
            continue;
        if(Ctx->DebugFuncs.count(f->getName()))
            continue;
        if(checkValidCaller(f, caller))
            EF.push_back(f);
    }

    while (!EF.empty()) {
        Function *TF = EF.front(); //Current checking value
		EF.pop_front();
            
        if (PF.find(TF) != PF.end())
			continue;
        PF.insert(TF);

        validcallers.insert(TF);
        for(auto it = Ctx->Callers[TF].begin(); it != Ctx->Callers[TF].end();it++){
            CallInst *caller = *it;
            Function *f = caller->getFunction();
            if(Ctx->ReleaseFuncSet.count(f->getName()) == 1)
                continue;
            if(Ctx->DebugFuncs.count(f->getName()))
                continue;
            if(checkValidCaller(f, caller))
                EF.push_back(f);
        }
    }
}

void WrapperAnalysisPass::identifyResourceFuncs(Function *F){
    if(!F)
        return;
    
    //First collect all F arguments related values
    if(F->arg_size() == 0)
        return;

    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();

    for(auto it = F->arg_begin(); it != F->arg_end();it++){

        Type *arg_type = it->getType();
        if(arg_type->isPointerTy() || arg_type->isStructTy()){
            EV.push_back(it);
        }
    }

    int validargnum = EV.size();

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
            
            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(U);
            if(GEP){
                if(!U_type->isPointerTy() && !U_type->isStructTy())
                    continue;
                EV.push_back(U);
                continue;
            }

            LoadInst* LI = dyn_cast<LoadInst>(U);
            if(LI){
                if(!U_type->isPointerTy() && !U_type->isStructTy())
                    continue;
                EV.push_back(U);
                continue;
            }

            BitCastInst *BCI = dyn_cast<BitCastInst>(U);
            if(BCI){
                if(!U_type->isPointerTy() && !U_type->isStructTy())
                    continue;
                EV.push_back(U);
                continue;
            }

            PHINode *PN = dyn_cast<PHINode>(U);
            if(PN){
                if(!U_type->isPointerTy() && !U_type->isStructTy())
                    continue;
                EV.push_back(U);
                continue;
            }
            
            //Find release funcs
            CallInst *CAI = dyn_cast<CallInst>(U);
            if(CAI){

                StringRef BB_FName = getCalledFuncName(CAI);
                if(BB_FName.contains("free") || BB_FName.contains("release")){

                    Ctx->ReleaseFuncSet.insert(BB_FName);

                    if(Ctx->ReleaseFuncSet.count(F->getName()) == 1)
                        continue;
                    if(Ctx->DebugFuncs.count(F->getName()))
                        continue;

                    //if(validargnum >=2)
                    //    continue;

                    Ctx->ReleaseFuncSet.insert(F->getName());
                    set<Function *> validcallers;
                    findAllValidCallers(F,CAI,validcallers);
                    for(auto it = validcallers.begin();it != validcallers.end();it++){
                        Function *f = *it;
                        //OP<<"F: "<<f->getName()<<"\n";
                        Ctx->ReleaseFuncSet.insert(f->getName());
                    }
                }
                
                if(BB_FName.contains("_get_drvdata")){
                    EV.push_back(U);
                    continue;
                }
                
            }
        }
    }
}

bool WrapperAnalysisPass::doInitialization(Module *M) {
  return false;
}

bool WrapperAnalysisPass::doFinalization(Module *M) {
  return false;
}

bool WrapperAnalysisPass::doModulePass(Module *M) {

    //Find function wrappers for each function
	for(Module::iterator f = M->begin(), fe = M->end();
			f != fe; ++f) {
		Function *F = &*f;

		if (F->empty())
			continue;
        
        //OP << F->getName() <<"\n";
        
        //Skip functions in skipfunc list
        if(1 == Ctx->SkipFuncs.count(F->getName()))
            continue;

		if (F->size() > MAX_BLOCKS_SUPPORT)
			continue;

        //Test for one function
#ifdef TEST_ONE_CASE
        if(F->getName()!= TEST_ONE_CASE){
            continue;
        }
#endif

        identifyResourceFuncs(F);
	}
	return false;
}