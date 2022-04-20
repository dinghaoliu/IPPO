CUR_DIR = $(shell pwd)
LLVM_BUILD := ${CUR_DIR}/llvm/build
SRC_DIR := ${CURDIR}/src
SRC_BUILD := ${CURDIR}/build

UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
	NPROC := ${shell nproc}
else
	NPROC := ${shell sysctl -n hw.ncpu}
endif

build_src_func = \
	(mkdir -p ${2} \
		&& cd ${2} \
		&& PATH=${LLVM_BUILD}/bin:${PATH}\
			LLVM_ROOT_DIR=${LLVM_BUILD}/bin \
			LLVM_LIBRARY_DIRS=${LLVM_BUILD}/lib \
			LLVM_INCLUDE_DIRS=${LLVM_BUILD}/include \
			CC=clang CXX=clang++ \
			cmake ${1} \
				-DCMAKE_BUILD_TYPE=Release \
        -DCMAKE_CXX_FLAGS_RELEASE="-std=c++14 -fno-rtti -fpic -g -O3 -fopenmp" \
		&& make -j${NPROC})

all: analyzer

analyzer:
	echo ${LLVM_BUILD}
	$(call build_src_func, ${SRC_DIR}, ${SRC_BUILD})

clean:
	rm -rf ${SRC_BUILD}
