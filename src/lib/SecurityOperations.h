#ifndef _SECURITY_OPERATIONS_H
#define _SECURITY_OPERATIONS_H

#include "Analyzer.h"
#include "Common.h"
#include "Tools.h"

class SecurityOperationsPass : public IterativeModulePass {

    typedef std::pair<BasicBlock*, BasicBlock*> Blockpair;
    typedef std::map<Blockpair, bool> ConnectGraph;
    typedef std::pair<Instruction *, BasicBlock *> CFGEdge;
    typedef std::map<CFGEdge, int> EdgeIgnoreMap;

    private:

    bool updateConnectGraph(ConnectGraph &connectGraph, 
        std::vector<BasicBlock*> globalblockset);

    void initConnectGraph(Function *F,ConnectGraph &connectGraph,
        std::vector<BasicBlock*> globalblockset,
        EdgeIgnoreMap edgeIgnoreMap);
    
    void identifyRefcountFuncs(Function *F,
        set<SecurityOperation *> &SecurityOperationSet);
    
    void identifyResourceAcquisition(Function *F,
        set<SecurityOperation *> &SecurityOperationSet);
    
    void identifyInitialization(Function *F,
        set<SecurityOperation *> &SecurityOperationSet);
    
    void identifyLockUnlock(Function *F,
        set<SecurityOperation *> &SecurityOperationSet);
    
    Value *findlastuse(Function *F, Value *V);
    bool checkvaliduse(Value *V);

    public:
        SecurityOperationsPass(GlobalContext *Ctx_)
         : IterativeModulePass(Ctx_, "SecurityOperations") { }
        virtual bool doInitialization(llvm::Module *);
        virtual bool doFinalization(llvm::Module *);
        virtual bool doModulePass(llvm::Module *);

        // Identify security checks.
	    void identifySecurityOperations(Function *F);

};
#endif