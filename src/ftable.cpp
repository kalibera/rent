
/* function table */

#include "ftable.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>

#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/SourceMgr.h>

#include <set>
#include <unordered_set>
#include <vector>

using namespace llvm;

const bool DEBUG = false;

bool readFunctionTable(Module *m, FunctionTableTy& tbl) {
  tbl.clear();
  GlobalVariable *ft = m->getGlobalVariable("R_FunTab", true);
  if (!ft) {
    errs() << "ERROR: Can't resolve FunTab\n";
    return false;
  }
  
  PointerType *pTy = dyn_cast<PointerType>(ft->getType());
  if (!pTy) {
    errs() << "ERROR: invalid function table (not pointer type)\n";
    return false;
  }
  ArrayType *aTy = dyn_cast<ArrayType>(pTy->getElementType());
  if (!aTy) {
    errs() << "ERROR: invalid function table (pointer not to array type)\n";
    return false;
  }
  
  unsigned nfuns = aTy->getNumElements();
  if (DEBUG) outs() << "Function table has " << std::to_string(nfuns) << " entries.\n";


  if (!ft->hasInitializer()) {
    errs() << "ERROR: invalid function table (does not have initializer)\n";
    return false;
  }
  
  ConstantArray *ca = dyn_cast<ConstantArray>(ft->getInitializer());
  if (!ca) {
    errs() << "ERROR: invalid function table (not constant array)\n";
    return false;
  }
  
  tbl.reserve(nfuns - 1);
  for(unsigned i = 0; i < nfuns - 1; i++) {
  
    ConstantStruct *cstr = dyn_cast<ConstantStruct>(ca->getAggregateElement(i));
    if (!cstr) {
      errs() << "ERROR: invalid function table (array not of structures): " << i << "\n";
      return false;
    }
    if (cstr->getType()->getName() != "struct.FUNTAB") {
      errs() << "ERROR: array of structures not struct.FUNTAB\n";
      return false;
    }
    ConstantExpr *nameExp = dyn_cast<ConstantExpr>(cstr->getAggregateElement(0U));
    Function *fun = dyn_cast<Function>(cstr->getAggregateElement(1U));
    ConstantInt *offsetC = dyn_cast<ConstantInt>(cstr->getAggregateElement(2U));
    ConstantInt *evalC = dyn_cast<ConstantInt>(cstr->getAggregateElement(3U));
    ConstantInt *arityC = dyn_cast<ConstantInt>(cstr->getAggregateElement(4U));
    
    int64_t offset = offsetC->getSExtValue();
    int64_t eval = evalC->getSExtValue();
    int64_t arity = arityC->getSExtValue();

    GlobalVariable* nameStr = cast<GlobalVariable>(nameExp->getOperand(0));
    ConstantDataArray* nameInit = cast<ConstantDataArray>(nameStr->getInitializer());
    std::string name = nameInit->getAsCString();
    
    if (DEBUG) errs() << " name: " << name << " function: " << fun->getName() <<  " offset: " << std::to_string(offset) 
      << " eval: " << std::to_string(eval) << " arity: " << std::to_string(arity) << "\n";
      
    tbl.push_back({FunctionEntry(name, fun, offset, eval, arity)});
    
  }
  if (!isa<ConstantAggregateZero>(ca->getAggregateElement(nfuns-1))) {
    errs() << "ERROR: last entry of function table is not zero\n";
    return false;
  }
  return true;  
}

bool dumpFunctions(FunctionTableTy& funtab, std::string type, bool isInternal, bool isPrimitive, bool isBuiltin, bool isSpecial) {
  unsigned cnt;
  
  cnt = 0;
  errs() << type << ":\n";
  for(FunctionTableTy::iterator fi = funtab.begin(), fe = funtab.end(); fi != fe; ++fi) {
    FunctionEntry& f = *fi;
    
    if (f.isInternal() == isInternal && f.isPrimitive() == isPrimitive && f.isBuiltin() == isBuiltin && f.isSpecial() == isSpecial) {
      cnt++;
      errs() << "  " << f.rname << " (" << f.fun->getName() << ":" << f.arity << " " /* << (ensuresArity(f.fun) ? "CHECKED" : "IGNORED") */ << ")\n";
    }
  }
  errs() << "  (in total " << std::to_string(cnt) << " " << type << ")\n";
  
}

void dumpFunctionTable(FunctionTableTy& funtab) {

  dumpFunctions(funtab, "internal builtins", true, false, true, false);
  dumpFunctions(funtab, "internal specials", true, false, false, true);
  dumpFunctions(funtab, "primitive builtins", false, true, true, false);
  dumpFunctions(funtab, "primitive specials", false, true, false, true);
}

int maxArity(Function* fun, FunctionTableTy& funtab) {

  int res = -1;
  for(FunctionTableTy::iterator fi = funtab.begin(), fe = funtab.end(); fi != fe; ++fi) {
    FunctionEntry& e = *fi;

    if (e.fun == fun && e.arity > res) {
      res = e.arity;
    }
  }
  return res;
}

IntSetTy uniqueFunctionArities(Function *fun, FunctionTableTy& funtab) {
  IntSetTy arities;
  
  for(FunctionTableTy::iterator fi = funtab.begin(), fe = funtab.end(); fi != fe; ++fi) {
    FunctionEntry& e = *fi;
    
    if (e.fun == fun) {
      arities.insert(e.arity);
    }
  }  
  return arities;
}

std::string dumpFunctionArities(IntSetTy arities, int effectiveArity) {

  assert(arities.size() > 0);
  if (arities.size() == 1) {
    int a = *arities.begin();
    if (a != effectiveArity) {
      return "[!" + std::to_string(a) + "]";
    } else {
      return "[" + std::to_string(a) + "]"; // perhaps could omit this output
    }
  }

  std::string res = "[";
  bool first = true;
  
  for(IntSetTy::iterator ai = arities.begin(), ae = arities.end(); ai != ae; ++ai) {
    int a = *ai;
    if (first) {
      first = false;
    } else {
      res += ",";
    }
    res += std::to_string(a);    
  }
  return res + "]";
}

bool isDoFunction(Function *fun, FunctionTableTy& funtab) {

  for(FunctionTableTy::iterator fi = funtab.begin(), fe = funtab.end(); fi != fe; ++fi) {
    FunctionEntry& e = *fi;
    Function *fun = e.fun;
    
    if (e.fun == fun) {
      return true;
    }
  }
  
  return false;
}
