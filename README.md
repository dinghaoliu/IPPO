# Detecting Missed Security Operations Through Differential Checking of Object-based Similar Paths

## How to use IPPO

### Build LLVM 
```sh 
	$ cd llvm 
	$ ./build-llvm.sh 
	# The installed LLVM is of version 9.0.0 
```

### Build the IPPO analyzer 
```sh 
	# Build the analysis pass of IPPO 
	$ cd ../analyzer 
	$ make 
	# Now, you can find the executable, `analyzer`, in `build/lib/`
```
 
### Prepare LLVM bitcode files of OS kernels

* Replace error-code definition files of the Linux kernel with the ones
in "encoded-errno"
* The code should be compiled with the built LLVM
* Compile the code with options: -O2, -g, -fno-inline
* Generate bitcode files
	- We have our own tool to generate bitcode files: https://github.com/sslab-gatech/deadline/tree/release/work. Note that files (typically less than 10) with compilation errors are simply discarded
	- We also provided the pre-compiled linux v5.3 bitcode files - https://github.com/umnsec/linux-bitcode

### Run the IPPO analyzer
```sh
	# To analyze a single bitcode file, say "test.bc", run:
	$ ./build/lib/analyzer -krc test.bc
	# To analyze a list of bitcode files, put the absolute paths of the bitcode files in a file, say "bc.list", then run:
	$ ./build/lib/analyzer -krc @bc.list
```

## More details

* [The IPPO paper (CCS'21)](https://nesa.zju.edu.cn/download/ldh_pdf_IPPO.pdf)
* To enable OpenMP for speeding up the analysis, please install openmp in your system, add '-fopenmp' to the Makefile, and enable the CONCURRENT macro in src/PairAnalysis/PairAnalysis.cc
* To generate the bug report into a local txt file, please enable the '#define OP in' macro in src/PairAnalysis/DifferentialCheck.cc
