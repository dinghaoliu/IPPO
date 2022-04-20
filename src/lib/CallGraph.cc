//===-- CallGraph.cc - Build global call-graph------------------===//
// 
// This pass builds a global call-graph. The targets of an indirect
// call are identified based on type-analysis, i.e., matching the
// number and type of function parameters.
//
//===-----------------------------------------------------------===//

#include <llvm/IR/DebugInfo.h>
#include <llvm/Pass.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/Instruction.h"
#include <llvm/Support/Debug.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Constants.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/CallGraph.h>
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/IR/BasicBlock.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include <llvm/IR/LegacyPassManager.h>
#include <map> 
#include <vector> 
#include "llvm/IR/CFG.h" 
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"

#include "CallGraph.h"
#include "Config.h"
#include "Common.h"

using namespace llvm;

//return true if sort successed, or return false (there is a loop inside function)
bool CallGraphPass::topSort(Function *F){
	if(!F){
		return true;
	}

	map<BasicBlock*,int> indegreeMap;
	BasicBlock* currentblock;
	indegreeMap.clear();

	//init
	for (Function::iterator b = F->begin(), e = F->end();
		b != e; ++b) {
        BasicBlock * B = &*b;
		pair<BasicBlock*,int> value(B,0);
        indegreeMap.insert(value);
    }

	//init indegreeMap
	for (Function::iterator b = F->begin(), e = F->end();
		b != e; ++b) {
        BasicBlock * B = &*b;

		for (BasicBlock *Succ : successors(B)) {
			if(Succ == B)
				continue;
			indegreeMap[Succ]++;
		}
    }

	bool found = false;
	while(!indegreeMap.empty()){

		found = false;
		//find a block with 0 indegree
		for(auto it = indegreeMap.begin(); it != indegreeMap.end(); it++){
			if(it->second==0){
				currentblock = it->first;
				found=true;
				break;
			}
		}

		if(!found){
			return false;
		}

		for (BasicBlock *Succ : successors(currentblock)) {
			if(Succ == currentblock)
				continue;
			indegreeMap[Succ]--;
		}

		indegreeMap.erase(currentblock);

	}
	return true;

}

// Find targets of indirect calls based on type analysis: as long as
// the number and type of parameters of a function matches with the
// ones of the callsite, we say the function is a possible target of
// this call.
void CallGraphPass::findCalleesByType(CallInst *CI, FuncSet &S) {

	if (CI->isInlineAsm())
		return;

	CallSite CS(CI);
	for (Function *F : Ctx->AddressTakenFuncs) {

		// VarArg
		if (F->getFunctionType()->isVarArg()) {
			// Compare only known args in VarArg.
		}
		// otherwise, the numbers of args should be equal.
		else if (F->arg_size() != CS.arg_size()) {
			continue;
		}

		if (F->isIntrinsic()) {
			continue;
		}

		// Type matching on args.
		bool Matched = true;
		CallSite::arg_iterator AI = CS.arg_begin();
		for (Function::arg_iterator FI = F->arg_begin(), 
				FE = F->arg_end();
				FI != FE; ++FI, ++AI) {
			// Check type mis-matches.
			// Get defined type on callee side.
			Type *DefinedTy = FI->getType();
			// Get actual type on caller side.
			Type *ActualTy = (*AI)->getType();

			if (DefinedTy == ActualTy)
				continue;

			// FIXME: this is a tricky solution for disjoint
			// types in different modules. A more reliable
			// solution is required to evaluate the equality
			// of two types from two different modules.
			// Since each module has its own type table, same
			// types are duplicated in different modules. This
			// makes the equality evaluation of two types from
			// two modules very hard, which is actually done
			// at link time by the linker.
			while (DefinedTy->isPointerTy() && ActualTy->isPointerTy()) {
				DefinedTy = DefinedTy->getPointerElementType();
				ActualTy = ActualTy->getPointerElementType();
			}
			if (DefinedTy->isStructTy() && ActualTy->isStructTy() &&
				(DefinedTy->getStructName().equals(ActualTy->getStructName())))
				continue;
			if (DefinedTy->isIntegerTy() && ActualTy->isIntegerTy() &&
				DefinedTy->getIntegerBitWidth() == ActualTy->getIntegerBitWidth())
				continue;
			// TODO: more types to be supported.

			// Make the type analysis conservative: assume universal
			// pointers, i.e., "void *" and "char *", are equivalent to 
			// any pointer type and integer type.
			if (
				(DefinedTy == Int8PtrTy &&
					(ActualTy->isPointerTy() || ActualTy == IntPtrTy)) 
				||
				(ActualTy == Int8PtrTy &&
					(DefinedTy->isPointerTy() || DefinedTy == IntPtrTy))
				)
				continue;
			else {
				#if 0 // for debugging
				if (F->getName().compare("nfs_fs_mount") == 0) {
				OP << "DefinedTy @ " << DefinedTy << ": " << *DefinedTy << "\n";
				OP << "ActualTy @ " << ActualTy << ": " << *ActualTy << "\n";
				}
				#endif
						Matched = false;
						break;
			}
		}

		if (Matched)
			S.insert(F);
	}
}

bool CallGraphPass::checkLoop(Function *F){
	if (F->isDeclaration())
		return false;

	DominatorTree DT = DominatorTree();
	DT.recalculate(*F);
	LoopInfo *LI = new LoopInfo();
	LI->releaseMemory();
	LI->analyze(DT);

	// Collect all loops in the function
	set<Loop *> LPSet;
	for (LoopInfo::iterator i = LI->begin(), e = LI->end(); i!=e; ++i) {

		Loop *LP = *i;
		LPSet.insert(LP);

		list<Loop *> LPL;

		LPL.push_back(LP);
		while (!LPL.empty()) {
			LP = LPL.front();
			LPL.pop_front();
			vector<Loop *> SubLPs = LP->getSubLoops();
			for (auto SubLP : SubLPs) {
				LPSet.insert(SubLP);
				LPL.push_back(SubLP);
			}
		}
	}

	if(LPSet.empty())
		return false;
	else{
		//OP << "Warning: loop failed once\n";
		int Loopnum = LPSet.size();
		for(Function::iterator b = F->begin(); 
            b != F->end(); b++){
			
			BasicBlock* bb = &*b;
			auto TI = bb->getTerminator();
			int NumSucc = TI->getNumSuccessors();
			
			if(NumSucc == 0)
				continue;

			for(BasicBlock *succblock : successors(bb)){
				
				if(succblock==bb){
					Loopnum--;
					continue;
				}
			}
		}

		if(Loopnum<1){
			return false;
		}
			
		else 
			return true;
	}

}

void CallGraphPass::unrollLoops(Function *F) {

	if (F->isDeclaration())
		return;

	DominatorTree DT = DominatorTree();
	DT.recalculate(*F);
	LoopInfo *LI = new LoopInfo();
	LI->releaseMemory();
	LI->analyze(DT);

	// Collect all loops in the function
	set<Loop *> LPSet;
	for (LoopInfo::iterator i = LI->begin(), e = LI->end(); i!=e; ++i) {

		Loop *LP = *i;
		LPSet.insert(LP);

		list<Loop *> LPL;

		LPL.push_back(LP);
		while (!LPL.empty()) {
			LP = LPL.front();
			LPL.pop_front();
			vector<Loop *> SubLPs = LP->getSubLoops();
			for (auto SubLP : SubLPs) {
				LPSet.insert(SubLP);
				LPL.push_back(SubLP);
			}
		}
	}

	for (Loop *LP : LPSet) {

		// Get the header,latch block, exiting block of every loop
		BasicBlock *HeaderB = LP->getHeader();

		unsigned NumBE = LP->getNumBackEdges();
		SmallVector<BasicBlock *, 4> LatchBS;

		LP->getLoopLatches(LatchBS);

		for (BasicBlock *LatchB : LatchBS) {
			if (!HeaderB || !LatchB) {
				OP<<"ERROR: Cannot find Header Block or Latch Block\n";
				continue;
			}

			// Two cases:
			// 1. Latch Block has only one successor:
			// 	for loop or while loop;
			// 	In this case: set the Successor of Latch Block to the 
			//	successor block (out of loop one) of Header block
			// 2. Latch Block has two successor: 
			// do-while loop:
			// In this case: set the Successor of Latch Block to the
			//  another successor block of Latch block 

			// get the last instruction in the Latch block
			Instruction *TI = LatchB->getTerminator();
			//int NumSucc = TI->getNumSuccessors();
			//OP << "Current TI Block-"<<getBlockName(LatchB)<<"\n";
			// Case 1:
			//Something wrong here!!!
			//If assume this is a for loop, then assume there must be one
			//successor of HeaderB can jump out the loop, which may be broken
			//by some goto instructions (no successor can jump out) 

			if (LatchB->getSingleSuccessor() != NULL) {
				int Numdominate = 0;
				
				for (succ_iterator sit = succ_begin(HeaderB); 
						sit != succ_end(HeaderB); ++sit) {  

					BasicBlock *SuccB = *sit;
					//OP << "SuccB: Block-"<<getBlockName(SuccB)<<"\n";	
					BasicBlockEdge BBE = BasicBlockEdge(HeaderB, SuccB);
					// Header block has two successor,
					// one edge dominate Latch block;
					// another does not.
					if (DT.dominates(BBE, LatchB)){
						continue;
					}
					else {
						Numdominate++;
						TI->setSuccessor(0, SuccB);
						//OP << "Changed TI: "<<*TI << "\n";
					}
				}

				//Special case: all successors fall in loop or out of loop
				//Equal to 0 or 2
				if(Numdominate!=1){
					//OP << "Abnormal Unroll Loop Case!\n";
					//Set the successor to be itself
					TI->setSuccessor(0, LatchB);
				}
			}
			// Case 2:
			else {
				//for (succ_iterator sit = succ_begin(LatchB); 
				//		sit != succ_end(LatchB); ++sit) {
				for (int i = 0; i < TI->getNumSuccessors(); ++i) {

					BasicBlock *SuccB = TI->getSuccessor(i);

					if (SuccB == HeaderB){
						BasicBlock* targetbb;
						if(i!=0)
							targetbb=TI->getSuccessor(0);
						else
							targetbb=TI->getSuccessor(1);

						Value *Cond = NULL;
						BranchInst *BI = dyn_cast<BranchInst>(TI);
						if(BI){
							if(BI->isConditional())
			    				Cond = BI->getCondition();
						}
						if(Cond){
							//OP<<"Cond: "<<*Cond << "\n";
							Constant *Ct = dyn_cast<Constant>(Cond);
							
							if(Ct && Ct->isOneValue() && targetbb != TI->getSuccessor(0)){
								//OP<<"This is invalid\n";
								continue;
							}
						}

						TI->setSuccessor(i, targetbb);
						//OP << "Changed TI: "<<*TI << "\n";
						continue;
					}
				}	
			}
		}

		//Execute the following part to make the loop execute at least once
		Instruction *HeaderB_TI = HeaderB->getTerminator();
		map<BasicBlock *,int> HeaderB_Follow_BBs;
		HeaderB_Follow_BBs.clear();
		for(int i = 0; i < HeaderB_TI->getNumSuccessors(); ++i){
			BasicBlock *SuccB = HeaderB_TI->getSuccessor(i);
			if(SuccB == HeaderB)
				continue;

			HeaderB_Follow_BBs[SuccB] = i;
		}

		for (BasicBlock *LatchB : LatchBS) {
			if (!HeaderB || !LatchB) {
				OP<<"ERROR: Cannot find Header Block or Latch Block\n";
				continue;
			}
			
			Instruction *LatchB_TI = LatchB->getTerminator();
			for (int i = 0; i < LatchB_TI->getNumSuccessors(); ++i) {
				BasicBlock *SuccB = LatchB_TI->getSuccessor(i);
				if(HeaderB_Follow_BBs.count(SuccB) != 0 && SuccB!= LatchB){
					HeaderB_TI->setSuccessor( HeaderB_Follow_BBs[SuccB],HeaderB);
				}
			}
		}
	}
}

bool CallGraphPass::doInitialization(Module *M) {

	DL = &(M->getDataLayout());
	Int8PtrTy = Type::getInt8PtrTy(M->getContext());
	IntPtrTy = DL->getIntPtrType(M->getContext());

	for (Function &F : *M) { 

		// Collect address-taken functions.
		if (F.hasAddressTaken()){
			Ctx->AddressTakenFuncs.insert(&F);
			Ctx->sigFuncsMap[funcHash(&F, false)].insert(&F);
		}	

		// Collect global function definitions.
		if (F.hasExternalLinkage() && !F.empty()) {
			// External linkage always ends up with the function name.
			StringRef FName = F.getName();
			// Special case: make the names of syscalls consistent.
			if (FName.startswith("SyS_"))
				FName = StringRef("sys_" + FName.str().substr(4));

			// Map functions to their names.
			Ctx->Funcs[FName] = &F;
		}

		// Keep a single copy for same functions (inline functions)
		size_t fh = funcHash(&F);
		if (Ctx->UnifiedFuncMap.find(fh) == Ctx->UnifiedFuncMap.end()) {
			Ctx->UnifiedFuncMap[fh] = &F;
			Ctx->UnifiedFuncSet.insert(&F);

			if (F.hasAddressTaken()) {
				Ctx->sigFuncsMap[funcHash(&F, false)].insert(&F);
			}
		}
	}

	return false;
}

bool CallGraphPass::doFinalization(Module *M) {
	return false;
}

bool CallGraphPass::doModulePass(Module *M) {

	// Use type-analysis to concervatively find possible targets of 
	// indirect calls.
	for (Module::iterator f = M->begin(), fe = M->end(); 
			f != fe; ++f) {

		Function *F = &*f;

		//Unroll loops
		unrollLoops(F);

		//Check the loop unroll result
		if(checkLoop(F)){
			OP << "Loop unroll failed!!!\n";
			Ctx->Loopfuncs.insert(F);
			continue;
		}
		else if(!topSort(F)){
			OP << "topSort not pass!!!\n";
			Ctx->Loopfuncs.insert(F);
			continue;
		}

		for (inst_iterator i = inst_begin(F), e = inst_end(F); 
				i != e; ++i) {
			// Map callsite to possible callees.
			if (CallInst *CI = dyn_cast<CallInst>(&*i)) {
				FuncSet FS;
				Function *CF = CI->getCalledFunction();
				if (!CF) {
#ifdef SOUND_MODE
					//findCalleesByType(CI, FS);
#endif
					Ctx->Callees[CI] = FS;

					for (Function *Callee : FS)
						Ctx->Callers[Callee].insert(CI);

					// Save called values for future uses.
					Ctx->IndirectCallInsts.push_back(CI);
				}
				// Direct call
				else {
					// Call external functions
          			if (CF->empty()) {
            			StringRef FName = CF->getName();
            			if (FName.startswith("SyS_"))
              				FName = StringRef("sys_" + FName.str().substr(4));
            			CF = Ctx->Funcs[FName];
          			}
					FS.insert(CF);
					Ctx->Callees[CI] = FS;
					Ctx->Callers[CF].insert(CI);
				}
			}
		}
	}

  return false;
}