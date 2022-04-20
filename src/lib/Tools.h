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
#include <llvm/Analysis/BasicAliasAnalysis.h>

#include "Analyzer.h"
#include "Common.h"
#include "Config.h"
#include "CallGraph.h"

//Used for debug
std::string getBlockName(BasicBlock *bb);

//Used for debug
std::string getValueName(Value* V);

//Used for debug
std::string getValueContent(Value* V);

//Used for debug
std::string getInstFilename(Instruction *I);

//Used for debug
unsigned getInstLineNo(Instruction *I);

//Used for debug
void printInstMessage(Instruction *inst);

//Used for debug
void printBlockMessage(BasicBlock *bb);

//Used for debug
void printBlockLineNoRange(BasicBlock *bb);

//Used for debug
void printFunctionMessage(Function *F);

//Find function calls in a basic block
void findFunctionCalls(BasicBlock *bb, 
    std::vector<llvm::Function *> &CallFunctionSet);

//Check if a basic block is a branch block
bool checkBranch(BasicBlock *bb);

//Init global baisc block set (just collect all basic blocks in a function)
void initGlobalBlockSet(Function *F, std::vector<BasicBlock*> &globalblockset);

//Check the line number of all insts in a basic block
//If all insts are at the same line, return the line number, else return -1
int checkBlockInstLocation(BasicBlock *bb);

//Check if there exits common element of two sets
bool findCommonOfSet(std::set<Value *> setA, std::set<Value *> setB);
bool findCommonOfSet(std::set<std::string> setA, std::set<std::string> setB);

// Check alias result of two values.
bool checkAlias(Value *, Value *, PointerAnalysisMap &);

bool checkStringContainSubString(string origstr, string targetsubstr);

//Check if there is a path from fromBB to toBB 
bool checkBlockPairConnectivity(BasicBlock* fromBB, BasicBlock* toBB);

bool checkValidCaller(Function *CallerF, CallInst *cai);
bool checkValidCaller(Value *V, CallInst *cai);