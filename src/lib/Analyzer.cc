//===-- Analyzer.cc - the Analyzer framework------------------------===//
// 
// This file implemets the Analyzer framework. It calls the pass for
// building call-graph and the pass for finding lacking security operation bugs.
//
//===-----------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"

#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>

#include "Analyzer.h"
#include "CallGraph.h"
#include "Config.h"
#include "WrapperAnalysis.h"
#include "SecurityOperations.h"
#include "SecurityChecks.h"
#include "PointerAnalysis.h"
#include "PairAnalysis/PairAnalysis.h"

#include <omp.h>

using namespace llvm;

// Command line parameters.
cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));

cl::opt<bool> CriticalVar(
    "krc", 
    cl::desc("Identify compiler-introduced TOCTTOU bugs"), 
    cl::NotHidden, cl::init(false));

GlobalContext GlobalCtx;


void IterativeModulePass::run(ModuleList &modules) {

	ModuleList::iterator i, e;
	OP << "[" << ID << "] Initializing " << modules.size() << " modules ";
	bool again = true;

	//Initialize
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			again |= doInitialization(i->first);
			OP << ".";
		}
	}
	OP << "\n";

	//Execute main analysis pass
	unsigned iter = 0, changed = 1;
	while (changed) {
		++iter;
		changed = 0;
		unsigned counter_modules = 0;
		unsigned total_modules = modules.size();

		//#pragma omp parallel for
		for (int it = 0; it < total_modules; ++it) {
			OP << "[" << ID << " / " << iter << "] ";
			OP << "[" << ++counter_modules << " / " << total_modules << "] ";
			OP << "[" << modules[it].second << "]\n";

			bool ret = doModulePass(modules[it].first);
			if (ret) {
				++changed;
				OP << "\t [CHANGED]\n";
			} else
				OP << "\n";
				
			//OP << "it: "<<it<<"Thread ID: "<< omp_get_thread_num()<<"\n";
		}
		OP << "[" << ID << "] Updated in " << changed << " modules.\n";
	}

	//Postprocessing
	OP << "[" << ID << "] Postprocessing ...\n";
	again = true;
	while (again) {
		again = false;
		for (i = modules.begin(), e = modules.end(); i != e; ++i) {
			// TODO: Dump the results.
			again |= doFinalization(i->first);
		}
	}

	OP << "[" << ID << "] Done!\n\n";
}

void LoadStaticData(GlobalContext *GCtx) {

	// Load skip functions
	SetSkipFuncs(GCtx->SkipFuncs);
	
	// Load auto freed alloc functions
	SetAutoFreedFuncs(GCtx->AutoFreedFuncs);

	// Set value escape functions
	SetEscapeFuncs(GCtx->EscapeFuncs);

	// Load member get functions
	SetMemberGetFuncs(GCtx->MemberGetFuncs);

	// Load error-handling functions
	SetErrorHandleFuncs(GCtx->ErrorHandleFuncs);

	SetRefcountRelatedFuncs(GCtx->RefcountRelatedFuncs);

	// load functions that copy/move values
	SetCopyFuncs(GCtx->CopyFuncs);

	// load llvm debug functions
	SetDebugFuncs(GCtx->DebugFuncs);

	// load init functions
	SetInitFuncs(GCtx->InitFuncs);

	// load heap alloc functions
	SetHeapAllocFuncs(GCtx->HeapAllocFuncs);

	// load pair functions
	SetPairFuncs(GCtx->PairFuncs, GCtx->PairFuncs_Lead);

	// load refcount functions
	SetRefcountFuncs(GCtx->RefcountFuncs);

	// load ignore instructions
	SetBinaryOperandInsts(GCtx->BinaryOperandInsts);

	// load ignore instructions
	SetSingleOperandInsts(GCtx->SingleOperandInsts);

	// Load test functions
	SetTestFuncs(GCtx->TestFuncs);

}

void PrintResults(GlobalContext *GCtx) {

	OP<<"############## Result Statistics ##############\n";
	OP<<"# Number of security checks: \t\t\t"<<GCtx->NumSecurityChecks<<"\n";
	OP<<"# Number of path pairs: \t\t\t"<<GCtx->NumPathPairs<<"\n";
	OP<<"# Number of all functions: \t\t\t"<<GCtx->NumFunctions<<"\n";
	OP<<"# Number of loop functions: \t\t\t"<<GCtx->Loopfuncs.size()<<"\n";
	OP<<"# Number of long functions: \t\t\t"<<GCtx->Longfuncs.size()<<"\n";
	OP<<"# Number of bugs:           \t\t\t"<<GCtx->NumBugs<<"\n";
	OP<<"# Number of all Path Pairs: \t\t\t"<<GCtx->NumPath<<"\n";

	OP<<"\n############## Security Operation Statistics ##############\n";
	OP<<"# Number of RefcountFuncs: \t\t\t"<<GCtx->NumRefcountFuncs<<"\n";
	OP<<"# Number of NumResourceAcq: \t\t\t"<<GCtx->NumResourceAcq<<"\n";
	OP<<"# Number of ReleaseFuncs: \t\t\t"<<GCtx->NumReleaseFucs<<"\n";
	OP<<"# Number of UnlockFuncs:  \t\t\t"<<GCtx->NumLockRelatedFucs<<"\n";

	int totalnum = 0;
	for(auto i = GCtx->SecurityOperationSets.begin(); i!=GCtx->SecurityOperationSets.end();i++){
		int num = i->second.size();
		totalnum +=num;
	}

	OP<<"# Total security operations: \t\t\t"<<totalnum<<"\n";

}


int main(int argc, char **argv) {
	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);

	llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

	cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
	SMDiagnostic Err;

	// Loading modules
	OP << "Total " << InputFilenames.size() << " file(s)\n";

	// Time Statistics
	clock_t start_time, finish_time;

	start_time = clock();
	for (unsigned i = 0; i < InputFilenames.size(); ++i) {

		LLVMContext *LLVMCtx = new LLVMContext();
		std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

		if (M == NULL) {
			OP << argv[0] << ": error loading file '"
				<< InputFilenames[i] << "'\n";
			continue;
		}

		Module *Module = M.release();
		StringRef MName = StringRef(strdup(InputFilenames[i].data()));
		GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
		GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

	}

	// Main workflow
	LoadStaticData(&GlobalCtx);

	finish_time = clock();
	GlobalCtx.Load_time = (double)(finish_time - start_time) / CLOCKS_PER_SEC;


	start_time = clock();
	// Build global callgraph.
	CallGraphPass CGPass(&GlobalCtx);
	CGPass.run(GlobalCtx.Modules);
	finish_time = clock();
	GlobalCtx.unroll_time = (double)(finish_time - start_time) / CLOCKS_PER_SEC;

	start_time = clock();
	WrapperAnalysisPass WAPass(&GlobalCtx);
	WAPass.run(GlobalCtx.Modules);
	finish_time = clock();
	GlobalCtx.wrapper_detect_time = (double)(finish_time - start_time) / CLOCKS_PER_SEC;

	if(CriticalVar){
		//Consider write one pass for every security operation

		//Find security checks
		SecurityChecksPass SCPass(&GlobalCtx);
		SCPass.run(GlobalCtx.Modules);

		// Pointer analysis
    	PointerAnalysisPass PTAPass(&GlobalCtx);
    	PTAPass.run(GlobalCtx.Modules);

		//Find security operations
		SecurityOperationsPass SOPass(&GlobalCtx);
		SOPass.run(GlobalCtx.Modules);

		//Excute path pair collection and comparition
		PairAnalysisPass PAPass(&GlobalCtx);
		PAPass.run(GlobalCtx.Modules);
	}

	PrintResults(&GlobalCtx);
	return 0;
}

