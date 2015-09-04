
#include "dofunc.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>

#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/SourceMgr.h>

#include <unordered_set>
#include <vector>

using namespace llvm;

const bool DEBUG = false;

// FIXME: how to print type name using the LLVM's custom rtti?
void check_type(Value *v) {

  #define CTSTRINGIFY(x) #x
  #define CTTOSTRING(x) CTSTRINGIFY(x)
  #define CT(x)  do { if (dyn_cast<x>(v) != NULL) { errs() << CTTOSTRING(x)  << "\n"; } } while(0);
  
  CT(Constant)
  
  CT(BlockAddress)
  CT(ConstantAggregateZero)
  CT(ConstantArray)
  CT(ConstantDataSequential)
  CT(ConstantExpr)
  CT(ConstantFP)
  CT(ConstantInt)
  CT(ConstantPointerNull)
  CT(ConstantStruct)
  CT(ConstantVector)
  CT(GlobalValue)
  CT(UndefValue)
    
  #undef CT
  #undef CTTOSTRING
  #undef CTSTRINGIFY
}

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

typedef std::vector<FunctionEntry> FunctionTableTy;

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
      errs() << "  " << f.rname << " (" << f.fun->getName() << ":" << f.arity << " " << (ensuresArity(f.fun) ? "CHECKED" : "IGNORED") << ")\n";
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

int main(int argc, char* argv[]) {

  LLVMContext context;
  if (argc != 2) {
    errs() << "Usage: einfo R.bin.bc\n";
    return 2;
  }

  SMDiagnostic error;
  std::string bcFName = argv[1];
  
  Module* m = parseIRFile(bcFName, error, context).release(); // FIXME: m is not freed at exit
  if (!m) {
    errs() << "ERROR: Cannot read IR file " << bcFName << "\n";
    error.print(argv[0], errs());
    return 2;
  }
  
  FunctionTableTy funtab;
  if (!readFunctionTable(m, funtab)) {
    errs() << "Could not read function table.\n";
    return 2;
  }

  if (0) {
      dumpFunctionTable(funtab);
  }
  
  if (0) {
    errs() << analyzeDoFunction(m->getFunction("do_return")).str() << "\n";
  }
    
  if (1) {

    typedef std::unordered_set<Function*> FunctionSetTy;
    FunctionSetTy analyzed;
    
    for(FunctionTableTy::iterator fi = funtab.begin(), fe = funtab.end(); fi != fe; ++fi) {
      FunctionEntry& e = *fi;
      Function *fun = e.fun;
      
      auto fsearch = analyzed.find(fun);
      if (fsearch == analyzed.end()) {
        analyzed.insert(fun);
        DoFunctionInfo nfo = analyzeDoFunction(fun);

        int nominalArity = maxArity(fun, funtab);
        
        if (0) {
          if (nominalArity != -1 && nominalArity < nfo.effectiveArity && !nfo.complexUseOfArgs) {
            // possible error in function table
          
            outs() << "ERROR: function " << fun->getName() << " has nominal arity " << std::to_string(nominalArity) <<
              " but effective arity " << std::to_string(nfo.effectiveArity) << " (" << nfo.str() << ")\n";

          } else if (nfo.effectiveArity < nominalArity && !nfo.complexUseOfArgs) {
            // error in function table or unused arguments

            outs() << "WARNING: function " << fun->getName() << " has nominal arity " << std::to_string(nominalArity) <<
              " but effective arity " << std::to_string(nfo.effectiveArity) << " (" << nfo.str() << ")\n";
          }
        }
        
        errs() << nfo.str() << "\n"; 
      }
    }
  }

  return 0;
}
