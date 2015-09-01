#ifndef RENT_DOFUNC_H
#define RENT_DOFUNC_H

#include <llvm/IR/Function.h>

using namespace llvm;

bool ensuresArity(Function *fun);

struct DoFunctionInfo {

  bool checkArityCalled;
  bool callEscapes;
  bool opEscapes;
  bool argEscapes;
  bool envEscapes;
  int effectiveArity;
};

DoFunctionInfo analyzeDoFunction(Function *fun);


#endif