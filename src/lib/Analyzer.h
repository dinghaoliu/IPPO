#ifndef _ANALYZER_GLOBAL_H
#define _ANALYZER_GLOBAL_H

#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include "llvm/Support/CommandLine.h"
#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>

#include "Common.h"


// 
// typedefs
//
typedef std::vector< std::pair<llvm::Module*, llvm::StringRef> > ModuleList;
// Mapping module to its file name.
typedef std::unordered_map<llvm::Module*, llvm::StringRef> ModuleNameMap;
// The set of all functions.
typedef llvm::SmallPtrSet<llvm::Function*, 8> FuncSet;
// Mapping from function name to function.
typedef std::unordered_map<std::string, llvm::Function*> NameFuncMap;
typedef llvm::SmallPtrSet<llvm::CallInst*, 8> CallInstSet;
typedef llvm::DenseMap<llvm::Function*, CallInstSet> CallerMap;
typedef llvm::DenseMap<llvm::CallInst *, FuncSet> CalleeMap;
// Pointer analysis types.
typedef std::map<llvm::Value *, std::set<llvm::Value *>> PointerAnalysisMap;
typedef std::map<llvm::Function *, PointerAnalysisMap> FuncPointerAnalysisMap;
typedef std::map<llvm::Function *, AAResults *> FuncAAResultsMap;
typedef std::map<llvm::Function *, PointerAnalysisMap> FuncStructAnalysisMap;

struct GlobalContext {

	GlobalContext() {
		// Initialize statistucs.
		NumFunctions = 0;
		NumSecurityChecks = 0;

		NumPathPairs = 0;

		Modules.clear();
		ModuleMaps.clear();

		Loopfuncs.clear();
		Longfuncs.clear();

	}

	unsigned NumFunctions;
	unsigned NumSecurityChecks;

	set<string> SkipFuncs;
	set<string> TestFuncs;
	set<string> AutoFreedFuncs;
	set<string> EscapeFuncs;
	set<string> MemberGetFuncs;

	// Map global function name to function defination.
	NameFuncMap Funcs;

	// Functions whose addresses are taken.
	FuncSet AddressTakenFuncs;

	// Map a callsite to all potential callee functions.
	CalleeMap Callees;

	// Map a function to all potential caller instructions.
	CallerMap Callers;

	// Indirect call instructions.
	std::vector<CallInst *>IndirectCallInsts;

	// Modules.
	ModuleList Modules;
	ModuleNameMap ModuleMaps;
	std::set<std::string> InvolvedModules;

	std::map<std::string, uint8_t> MemWriteFuncs;
	std::set<std::string> CriticalFuncs;

	// Pinter analysis results.
	FuncPointerAnalysisMap FuncPAResults;
	FuncAAResultsMap FuncAAResults;
	FuncStructAnalysisMap FuncStructResults;

	/******SecurityCheck methods******/

	// Unified functions -- no redundant inline functions
	DenseMap<size_t, Function *>UnifiedFuncMap;
	set<Function *>UnifiedFuncSet;

	// Map function signature to functions
	DenseMap<size_t, FuncSet>sigFuncsMap;

	// SecurityChecksPass
	// Functions handling errors
	set<string> ErrorHandleFuncs;
	set<string> RefcountRelatedFuncs;
	map<string, tuple<int8_t, int8_t, int8_t>> CopyFuncs;

	// Identified sanity checks
	DenseMap<Function *, set<SecurityCheck>> SecurityCheckSets;
	DenseMap<Function *, set<Value *>> CheckInstSets;

	//Todo: Add other security operation check methods

	/******Security operation methods******/
	unsigned NumRefcountFuncs = 0;
	unsigned NumResourceAcq = 0;
	unsigned NumReleaseFucs = 0;
	unsigned NumLockRelatedFucs = 0;

	map<string, pair<uint8_t, int8_t>> InitFuncs;
	set<string> HeapAllocFuncs;
	map<string, set<string>> PairFuncs;
	set<string> PairFuncs_Lead;
	map<string, set<string>> RefcountFuncs;

	//Identify security operations
	DenseMap<Function *, set<SecurityOperation>> SecurityOperationSets;
	set<string> ReleaseFuncSet;

	/******Path pair analysis methods******/
	unsigned NumPathPairs = 0;
	unsigned long long NumPath = 0;
	unsigned long long NumBlock = 0;
	unsigned long long NumInst = 0;
	unsigned NumBugs = 0;
	set<Function *> Loopfuncs;
	set<Function *> Longfuncs;
	set<string> DebugFuncs;
	set<string> BinaryOperandInsts;
	set<string> SingleOperandInsts;

	/******Time analysis methods******/
	double Load_time = 0;
	double unroll_time = 0;
	double wrapper_detect_time = 0;
	double release_detect_time = 0;
	double refcount_detect_time = 0;
	double error_edge_identify_time = 0;
	double FE_graphe_generate_time = 0;
	double FE_path_collect_time = 0;
	double cross_check_time = 0;
	double security_check_time = 0;
	double security_check_analysis = 0;

};

class IterativeModulePass {
	protected:
		GlobalContext *Ctx;
		const char * ID;
	public:
		IterativeModulePass(GlobalContext *Ctx_, const char *ID_)
			: Ctx(Ctx_), ID(ID_) { }

		// Run on each module before iterative pass.
		virtual bool doInitialization(llvm::Module *M)
		{ return true; }

		// Run on each module after iterative pass.
		virtual bool doFinalization(llvm::Module *M)
		{ return true; }

		// Iterative pass.
		virtual bool doModulePass(llvm::Module *M)
		{ return false; }

		virtual void run(ModuleList &modules);
};

#endif
