#ifndef RENT_DOFUNC_H
#define RENT_DOFUNC_H

#include <llvm/IR/Function.h>

#include <unordered_map>

using namespace llvm;

bool ensuresArity(Function *fun);

// CAD<n>R(var) list access
struct ListAccess {
  std::string varName;	// variable in which the list is stored
  bool isArgsVar;	// is the variable (list) the "args" argument of the do_XXX function?
  unsigned line;	// line number at which (the load of the access) is
  unsigned ncdrs;	// number of "D"s in the expression
  
  ListAccess() { markUnknown(); }
  
  bool isUnknown() const { return line == 0; }

  void markUnknown() {
    varName = "";
    isArgsVar = false;
    line = 0;
    ncdrs = 0;
  }
  
  std::string str() {
    if (isUnknown()) {
      return "UNKNOWN";
    }
    std::string pref = "CA";
    std::string suff = "):" + std::to_string(line);
    for(unsigned i = 0; i < ncdrs; i++) {
      pref += "D";
    }
    return pref + "R(" + varName + suff;
  }
};

struct ListAccess_equal {
  bool operator() (const ListAccess& lhs, const ListAccess& rhs) const;
};

struct ListAccess_hash {
  size_t operator()(const ListAccess& t) const;
};

typedef std::unordered_map<ListAccess, unsigned, ListAccess_hash, ListAccess_equal> ResolvedListAccessesTy;

struct DoFunctionInfo {

  bool checkArityCalled; // on all returning paths
  int effectiveArity;    // maximum index of argument value used + 1
  bool usesTags;	 // a tag may be used
  bool computesArgsLength;	// uses length on args (or some suffix of it)

  bool complexUseOfArgs; // anything except loading arg value, arg tag, calling checkArity
  bool complexUseOfOp;   // any use except checkArity
  bool complexUseOfCall;
  bool complexUseOfEnv;
  
  ResolvedListAccessesTy listAccesses;
  
  Function *fun;
  
  DoFunctionInfo(Function *fun): fun(fun), checkArityCalled(false), effectiveArity(-1), usesTags(true), computesArgsLength(true),
    complexUseOfArgs(true), complexUseOfCall(true), complexUseOfEnv(true), listAccesses()  {}; // conservative defaults
    
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
      if (computesArgsLength) {
        res += " !length";
      }
    }
    if (complexUseOfEnv) {
      res += " !ENV";
    }
    return res;
  }
};

DoFunctionInfo analyzeDoFunction(Function *fun, bool resolveListAccesses = true);

#endif
