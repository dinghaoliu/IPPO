set (AnalyzerSourceCodes
  Common.h
  Common.cc
	Analyzer.h
	Analyzer.cc
	CallGraph.h
  CallGraph.cc
  Tools.h
  Tools.cc
  SecurityChecks.h
  SecurityChecks.cc
  WrapperAnalysis.cc
  WrapperAnalysis.h
  SecurityOperations.h
  SecurityOperations.cc
  PointerAnalysis.h
  PointerAnalysis.cc
  PairAnalysis/PairAnalysis.h
  PairAnalysis/PairAnalysis.cc
  PairAnalysis/PathCollection.cc
  PairAnalysis/ReturnValueAnalysis.cc
  PairAnalysis/PairAnalysis_Tools.cc
  PairAnalysis/DataFlowAnalysis.cc
  PairAnalysis/DifferentialCheck.cc
)

#file(COPY configs/ DESTINATION configs)

# Build libraries.
add_library (AnalyzerObj OBJECT ${AnalyzerSourceCodes})
#add_library (Analyzer SHARED $<TARGET_OBJECTS:AnalyzerObj>)
add_library (AnalyzerStatic STATIC $<TARGET_OBJECTS:AnalyzerObj>)

# Build executable analyzer.
set (EXECUTABLE_OUTPUT_PATH ${UNISAN_BINARY_DIR})
link_directories (${UNISAN_BINARY_DIR}/lib)
add_executable(analyzer ${AnalyzerSourceCodes})
target_link_libraries(analyzer
  LLVMAsmParser 
  LLVMSupport 
  LLVMCore 
  LLVMAnalysis
  LLVMIRReader
  AnalyzerStatic
  )
