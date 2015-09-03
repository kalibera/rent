#ifndef RENT_DOFUNC_H
#define RENT_DOFUNC_H

#include <llvm/IR/Function.h>

using namespace llvm;

bool ensuresArity(Function *fun);

struct DoFunctionInfo {

  bool checkArityCalled; // on all returning paths
  int effectiveArity;    // maximum index of argument value used + 1
  bool usesTags;	 // a tag may be used

  bool complexUseOfArgs; // anything except loading arg value, arg tag, calling checkArity
  bool complexUseOfOp;   // any use except checkArity
  bool complexUseOfCall;
  bool complexUseOfEnv;
  
  Function *fun;
  
  DoFunctionInfo(Function *fun): fun(fun), checkArityCalled(false), effectiveArity(-1), usesTags(true), complexUseOfArgs(true),
    complexUseOfCall(true), complexUseOfEnv(true)  {}; // conservative defaults
    
  std::string str() {
    std::string res = fun->getName();
    if (complexUseOfCall) {
      res += " !CALL";
    }
    if (complexUseOfOp) {
      res += " !OP";
    }
    if (complexUseOfArgs) {
      res += " !ARGS";
    } else {
      if (checkArityCalled) {
        res += " +checkArity";
      }
      if (usesTags) {
        res += " !TAGS";
      }
      if (effectiveArity > -1) {
        res += " +" + std::to_string(effectiveArity);
      }
    }
    if (complexUseOfEnv) {
      res += " !ENV";
    }
    return res;
  }
};

DoFunctionInfo analyzeDoFunction(Function *fun);


#endif