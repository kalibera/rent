
# ---------------------

HOST := $(shell hostname -s)

ifeq ($(HOST), prg)
  LLVM := /home/tomas/work/opt/clang+llvm-3.6.1-x86_64-linux-gnu
  CXX := g++-4.8

else ifeq ($(HOST), r-lnx400)
  LLVM := /var/scratch/tomas/opt/llvm/clang+llvm-3.61-x86_64-fedora20
  CXX := g++

else
  # ------  CUSTOMIZE HERE --------- 
  # or provide these variables to make
  
  ifeq ($(wildcard $(LLVM)),)
    $(error Please customize your Makefile here. Please set the home directory for LLVM 3.6.1)
  endif

  CXX ?= g++
endif

# ---------------------

LLVMC := $(LLVM)/bin/llvm-config

CPPFLAGS := $(shell $(LLVMC) --cppflags)
CXXFLAGS := $(shell $(LLVMC) --cxxflags) -O3 -g3 -MMD
#CXXFLAGS := $(shell $(LLVMC) --cxxflags) -O0 -g3 -MMD

LDFLAGS := $(shell $(LLVMC) --ldflags)
LDLIBS := $(shell $(LLVMC) --libs --system-libs) 

LINK.o = $(LINK.cc) # link with C++ compiler by default

SOURCES := $(wildcard *.cpp)
DEPENDS := $(SOURCES:.cpp=.d)
OBJECTS := $(SOURCES:.cpp=.o)
SOBJECTS := $(filter-out %info.o, $(OBJECTS))

TOOLS := einfo

all: $(TOOLS)

einfo: einfo.o $(SOBJECTS)

clean:
	rm -f $(OBJECTS) $(DEPENDS) $(TOOLS)

-include $(DEPENDS)
