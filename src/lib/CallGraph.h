#ifndef _CALL_GRAPH_H
#define _CALL_GRAPH_H

#include "Analyzer.h"
#include "Tools.h"

class CallGraphPass : public IterativeModulePass {

	private:
		const DataLayout *DL;
		// char * or void *
		Type *Int8PtrTy;
		// long interger type
		Type *IntPtrTy;

		// Use type-based analysis to find targets of indirect calls
		void findCalleesByType(llvm::CallInst*, FuncSet&);

		void unrollLoops(Function *F);

		bool checkLoop(Function *F);

		bool topSort(Function *F);

	public:
		CallGraphPass(GlobalContext *Ctx_)
			: IterativeModulePass(Ctx_, "CallGraph") { }
		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);
};

#endif
