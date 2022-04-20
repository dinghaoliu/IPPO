#ifndef _WRAPPER_ANALYSIS_H
#define _WRAPPER_ANALYSIS_H

#include "Analyzer.h"
#include "Common.h"
#include "Tools.h"

class WrapperAnalysisPass : public IterativeModulePass {

    private:

        //Find release function wrappers
        void identifyResourceFuncs(Function *F);
        void findAllValidCallers(Function *F, CallInst *CAI, 
        set<Function *> &validcallers);
    

    public:
        WrapperAnalysisPass(GlobalContext *Ctx_)
         : IterativeModulePass(Ctx_, "WrapperAnalysis") { }
        virtual bool doInitialization(llvm::Module *);
        virtual bool doFinalization(llvm::Module *);
        virtual bool doModulePass(llvm::Module *);

};

#endif