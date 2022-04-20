#ifndef _POINTER_ANALYSIS_H
#define _POINTER_ANALYSIS_H

#include "Analyzer.h"


class PointerAnalysisPass : public IterativeModulePass {

    typedef std::pair<Value *, MemoryLocation *> AddrMemPair;

    typedef struct StructNode {
        
        set<Value *> NodeSet;
        set<Value *> MemberValueSet;
        set<StructNode*> MemberNodeSet;

        StructNode(){
            NodeSet.clear();
            MemberValueSet.clear();
            MemberNodeSet.clear();
        }

        void insert_member(Value * v){
            NodeSet.insert(v);
        }

        void mergeNode(StructNode n){

            NodeSet.insert(n.NodeSet.begin(), n.NodeSet.end());
            MemberNodeSet.insert(n.MemberNodeSet.begin(), n.MemberNodeSet.end());
        }

        int num_member_values(){
            int sum = 0;
            for(auto it = MemberNodeSet.begin(); it != MemberNodeSet.end(); it++){
                StructNode* membernode = *it;
                sum += membernode->NodeSet.size();
            }
            return sum;
        }

    }StructNode;
    
    
    private:
        TargetLibraryInfo *TLI;

        void detectAliasPointers(Function *, AAResults &,
                                PointerAnalysisMap &);
                            
        void detectAliasPointers_new(Function *, AAResults &,
                                PointerAnalysisMap &,
                                PointerAnalysisMap &);

        void detectStructRelation(Function *F, PointerAnalysisMap &);
        void detectStructRelation_new(Function *F, PointerAnalysisMap &);

    public:
        PointerAnalysisPass(GlobalContext *Ctx_)
        : IterativeModulePass(Ctx_, "PointerAnalysis") { }
        virtual bool doInitialization(llvm::Module *);
        virtual bool doFinalization(llvm::Module *);
        virtual bool doModulePass(llvm::Module *);
};

#endif
