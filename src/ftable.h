#ifndef RENT_FTABLE_H
#define RENT_FTABLE_H

#include <llvm/IR/Function.h>

#include <set>
#include <vector>

using namespace llvm;

struct FunctionEntry {
  std::string rname;
  Function *fun;
  int offset;
  int eval;
  int arity;
  
  FunctionEntry(std::string rname, Function *fun, int offset, int eval, int arity):
    rname(rname), fun(fun), offset(offset), eval(eval), arity(arity) {}

  unsigned evalX() {
    return eval / 100;
  }
  
  unsigned evalY() {
    return (eval % 100) / 10;
  }
  
  unsigned evalZ() {
    return eval % 10;
  }
  
  bool isInternal() {
    return evalY() == 1;
  }
  
  bool isPrimitive() {
    return evalY() != 1;
  }
  
  bool isBuiltin() {
    return evalZ() == 1;
  }
  
  bool isSpecial() {
    return evalZ() == 0;
  }
};

typedef std::vector<FunctionEntry> FunctionTableTy; // the parsed function "table"

bool readFunctionTable(Module *m, FunctionTableTy& tbl);
void dumpFunctionTable(FunctionTableTy& funtab);

typedef std::set<int> IntSetTy;

int maxArity(Function* fun, FunctionTableTy& funtab);
IntSetTy uniqueFunctionArities(Function *fun, FunctionTableTy& funtab);
std::string dumpFunctionArities(IntSetTy arities, int effectiveArity);

#endif
