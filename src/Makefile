
# The support for rewriting using CLANG API no longer builds with LLVM
# because of incompatible changes in LLVM; it would have to be ported to
# newer versions if needed.

# The part that does just the analysis using LLVM bitcode is still working
# and on Ubuntu 16.04.2 only needs the LLVM installation that is part of Ubuntu

# ---------------------

HOST := $(shell hostname -s)

ifeq ($(HOST), prg)
  #LLVM := /home/tomas/work/opt/clang+llvm-3.6.1-x86_64-linux-gnu
  LLVM := /home/tomas/work/opt/clang+llvm-3.8.1-x86_64-linux-gnu-ubuntu-16.04
    # Ubuntu 16.04.2
  #LLVM := /usr
  #CXX := g++-4.8
  CXX := g++

else ifeq ($(HOST), r-lnx400)
  LLVM := /var/scratch/tomas/opt/llvm/clang+llvm-3.61-x86_64-fedora20
  CXX := g++

else
  # ------  CUSTOMIZE HERE --------- 
  # or provide these variables to make
  
  ifeq ($(wildcard $(LLVM)),)
    $(error Please customize your Makefile here. Please set the home directory for LLVM 3.8)
  endif

  CXX ?= g++
endif

# ---------------------

LLVMC := $(LLVM)/bin/llvm-config

CPPFLAGS := $(shell $(LLVMC) --cppflags) -I/usr/include/libcxxabi
CXXFLAGS := $(shell $(LLVMC) --cxxflags) -O3 -g3 -MMD -I/usr/include/libcxxabi -I/usr/include/llvm-3.8
#CXXFLAGS := $(shell $(LLVMC) --cxxflags) -O0 -g3 -MMD

# for GCC, which does not support this warning
CXXFLAGS := $(filter-out -Wcovered-switch-default, $(CXXFLAGS))

# clang libraries are only needed for the rewriting
CLANG_LIBS := \
	-Wl,--start-group \
	-lclangAST \
	-lclangAnalysis \
	-lclangBasic \
	-lclangDriver \
	-lclangEdit \
	-lclangFrontend \
	-lclangFrontendTool \
	-lclangLex \
	-lclangParse \
	-lclangSema \
	-lclangEdit \
	-lclangASTMatchers \
	-lclangRewrite \
	-lclangRewriteFrontend \
	-lclangStaticAnalyzerFrontend \
	-lclangStaticAnalyzerCheckers \
	-lclangStaticAnalyzerCore \
	-lclangSerialization \
	-lclangToolingCore \
	-lclangTooling \
	-Wl,--end-group
	
LDFLAGS := $(shell $(LLVMC) --ldflags)
#LDLIBS := $(CLANG_LIBS) $(shell $(LLVMC) --libs --system-libs)
LDLIBS := $(shell $(LLVMC) --libs --system-libs)

LINK.o = $(LINK.cc) # link with C++ compiler by default

SOURCES := $(wildcard *.cpp)
DEPENDS := $(SOURCES:.cpp=.d)
OBJECTS := $(SOURCES:.cpp=.o)

SOBJECTS := $(filter-out arewriter.o %sample.o %info.o, $(OBJECTS))

TOOLS := einfo
# tooling_sample arg_patterns_sample arewriter 
#   do the rewriting
#TOOLS := einfo tooling_sample arg_patterns_sample arewriter

all: $(TOOLS)

einfo: einfo.o $(SOBJECTS)

tooling_sample: tooling_sample.o $(SOBJECTS)

arg_patterns_sample: arg_patterns_sample.o $(SOBJECTS)

arewriter: arewriter.o $(SOBJECTS)

clean:
	rm -f $(OBJECTS) $(DEPENDS) $(TOOLS)

-include $(DEPENDS)
