#include "Tools.h"

//#define DEBUG_PRINT 0

//Used for debug
unsigned getInstLineNo(Instruction *I){

    begin:

    if(!I)
        return 0;
        
    //DILocation *Loc = dyn_cast<DILocation>(N);
    DILocation *Loc = I->getDebugLoc();
    if (!Loc ){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    unsigned Number = Loc->getLine();

    if(Number < 1){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    return Number;
}

//Used for debug
std::string getInstFilename(Instruction *I){
    begin:

    if(!I)
        return "";

    DILocation *Loc = I->getDebugLoc();
    if (!Loc ){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    string Filename = Loc->getFilename();

    if(Filename.length() == 0){
        auto nextinst = I->getNextNonDebugInstruction();
        I = nextinst;
        goto begin;
    }

    return Filename;
}

//Used for debug
string getBlockName(BasicBlock *bb){
    if(bb == NULL)
        return "NULL block";
    std::string Str;
    raw_string_ostream OS(Str);
    bb->printAsOperand(OS,false);
    return OS.str();
}

//Used for debug
string getValueName(Value* V){
    std::string Str;
    raw_string_ostream OS(Str);
    V->printAsOperand(OS,false);
    return OS.str();
}

//Used for debug
std::string getValueContent(Value* V){
    std::string Str;
    raw_string_ostream OS(Str);
    V->print(OS,false);
    return OS.str();
}

//Used for debug
void printInstMessage(Instruction *inst){
    if(!inst){
        OP << "No such instruction";
        return;
    }
        
    MDNode *N = inst->getMetadata("dbg");

    if (!N)
        return;
    
    DILocation *Loc = dyn_cast<DILocation>(N);
    string SCheckFileName = Loc->getFilename().str();
    unsigned SCheckLineNo = Loc->getLine();
    OP << "LineNo: " << SCheckLineNo<<"\n";
}

//Used for debug
void printBlockMessage(BasicBlock *bb){

    if(!bb){
        OP << "No such block";
        return;
    }
    
    auto begininst = dyn_cast<Instruction>(bb->begin());
    auto endinst = bb->getTerminator();

    OP << "\nBegin at --- ";
    printInstMessage(begininst);
    OP << "End   at --- ";
    printInstMessage(endinst);
}

//Used for debug
void printBlockLineNoRange(BasicBlock *bb){
    if(!bb){
        OP << "No such block";
        return;
    }
    
    auto begininst = dyn_cast<Instruction>(bb->begin());
    auto endinst = bb->getTerminator();
    OP << "("<<getInstLineNo(begininst)<<"-"<<getInstLineNo(endinst)<<")";
}

//Used for debug
void printFunctionMessage(Function *F){

    if(!F)
        return;
    
    for(Function::iterator b = F->begin(); 
        b != F->end(); b++){
        
        BasicBlock * bb = &*b;
        OP << "\nCurrent block: block-"<<getBlockName(bb)<<"\n";
        //printBlockMessage(bb);

        OP << "Succ block: \n";
        for (BasicBlock *Succ : successors(bb)) {
			//printBlockMessage(Succ);
            OP << " block-"<<getBlockName(Succ)<<" ";
		}
        OP<< "\n";
    }

}

//Find function calls in a basic block
void findFunctionCalls(BasicBlock * bb, 
    std::vector<llvm::Function *> &CallFunctionSet){
    
    CallInst *call_inst;
    InvokeInst *invoke_inst;//InvokeInst maybe unneeded for C programs

    //Go through all instructions
    for(BasicBlock::iterator i = bb->begin(); 
        i != bb->end(); i++){
        call_inst = dyn_cast<CallInst>(i);
        invoke_inst = dyn_cast<InvokeInst>(i);

        if(call_inst){
            Function* called_function = call_inst->getCalledFunction();

    #ifdef DEBUG_PRINT
            OP << "    Called functions: " 
                << called_function->getName() << "\n";
    #endif

            CallFunctionSet.push_back(called_function);
        }

        if(invoke_inst){
            Function* invoked_function = invoke_inst->getCalledFunction();

    #ifdef DEBUG_PRINT
            OP << "    Invoked functions: " 
                << invoked_function->getName() << "\n";
    #endif

            CallFunctionSet.push_back(invoked_function);
        }
    }
}

//Check if a basic block is a branch block
bool checkBranch(BasicBlock *bb){
    if(!bb)
        return false;
    
    auto TI = bb->getTerminator();
    int NumSucc = TI->getNumSuccessors();

    if(NumSucc>1)
        return true;
    else 
        return false;
}


//Init global baisc block set (just collect all basic blocks in a function)
void initGlobalBlockSet(Function *F, 
    std::vector<BasicBlock*> &globalblockset){
        
    globalblockset.clear();
    if(!F)
        return;
    
    for (Function::iterator b = F->begin(), e = F->end();
		b != e; ++b) {
        BasicBlock * B = &*b;
        globalblockset.push_back(B);
    }
}

//Check the line number of all insts in a basic block
//If all insts are at the same line, return the line number, else return -1
int checkBlockInstLocation(BasicBlock *bb){
    if(!bb)
        return -1;

    set<int> linenumset;
    linenumset.clear();
    
    for(BasicBlock::iterator i = bb->begin(); 
        i != bb->end(); i++){

        auto inst = dyn_cast<Instruction>(i);
        MDNode *N = inst->getMetadata("dbg");
        if (!N)
            continue;

        DILocation *Loc = dyn_cast<DILocation>(N);
        int SCheckLineNo = Loc->getLine();
        if(SCheckLineNo==0)
            continue;
        
        linenumset.insert(SCheckLineNo);
    }

    if(linenumset.size()==1){
        return (*linenumset.begin());
    }
    else
        return -1;
}

//Check if there exits common element of two sets
bool findCommonOfSet(set<Value *> setA, set<Value *> setB){
    if(setA.empty() || setB.empty())
        return false;
    
    bool foundtag = false;
    for(auto i = setA.begin(); i != setA.end(); i++){
        Value * vi = *i;
        for(auto j = setB.begin(); j != setB.end(); j++){
            Value * vj = *j;
            if(vi == vj){
                foundtag = true;
                return foundtag;
            }
        }
    }

    return foundtag;
}

bool findCommonOfSet(set<std::string> setA, set<std::string> setB){
    if(setA.empty() || setB.empty())
        return false;
    
    bool foundtag = false;
    for(auto i = setA.begin(); i != setA.end(); i++){
        string vi = *i;
        for(auto j = setB.begin(); j != setB.end(); j++){
            string vj = *j;
            if(vi == vj){
                foundtag = true;
                return foundtag;
            }
        }
    }

    return foundtag;
}


/// Check alias result of two values.
/// True: alias, False: not alias.
bool checkAlias(Value *Addr1, Value *Addr2,
		PointerAnalysisMap &aliasPtrs) {

	if (Addr1 == Addr2)
		return true;

	auto it = aliasPtrs.find(Addr1);
	if (it != aliasPtrs.end()) {
		if (it->second.count(Addr2) != 0)
			return true;
	}

	// May not need to do this further check.
	it = aliasPtrs.find(Addr2);
	if (it != aliasPtrs.end()) {
		if (it->second.count(Addr1) != 0)
			return true;
	}

	return false;
}


bool checkStringContainSubString(string origstr, string targetsubstr){
    
    if(origstr.length() == 0 || targetsubstr.length() == 0)
        return false;
    
    string::size_type idx;
    idx = origstr.find(targetsubstr);
    if(idx == string::npos)
        return false;
    else
        return true;
}

//Check if there is a path from fromBB to toBB 
bool checkBlockPairConnectivity(
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

//The CallerF needs to pass its arguments to cai, or it's invalid
bool checkValidCaller(Function *CallerF, CallInst *cai){
    if(!CallerF || !cai)
        return false;
    
    if(CallerF->arg_size() == 0)
        return false;
    
    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
    
    for(auto it = CallerF->arg_begin(); it != CallerF->arg_end();it++){

        Type *arg_type = it->getType();
        if(arg_type->isPointerTy() || arg_type->isStructTy()){
            EV.push_back(it);
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
                if(CAI == cai)
                    return true;

                StringRef FName = getCalledFuncName(CAI);
                if(checkStringContainSubString(FName,"_get_drvdata")){
                    EV.push_back(U);
                    continue;
                }
            }
        }
    }

    return false;
}

//Check if V is a arg of cai
bool checkValidCaller(Value *V, CallInst *cai){
    if(!V || !cai)
        return false;
    
    std::list<Value *> EV; //BFS record list
    std::set<Value *> PV; //Global value set to avoid loop
    EV.clear();
    PV.clear();
    
    EV.push_back(V);

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

            StoreInst *STI = dyn_cast<StoreInst>(U);
            if(STI){
                Value* pop = STI->getPointerOperand();
                if(auto CaI = dyn_cast<ConstantExpr>(pop)){
                    if(CaI->isCast()){
                        Instruction *inst = CaI->getAsInstruction();
                        if(inst){
                            auto BCI = dyn_cast<BitCastInst>(inst);
                            if(BCI){
                                Value *op = BCI->getOperand(0);
                                EV.push_back(op);
                            }
                        }
                    }
                }
                EV.push_back(pop);
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
                if(CAI == cai)
                    return true;
            }
        }
    }

    return false;
}