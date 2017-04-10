  
#include "dofunc.h"
#include "ftable.h"
#include "call.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>

#include <llvm/Support/raw_ostream.h>
#include <llvm/Support/Path.h>
#include <llvm/Support/SourceMgr.h>

#include <set>
#include <unordered_set>
#include <vector>

using namespace llvm;

const bool DEBUG = false;

// FIXME: how to print type name using the LLVM's custom rtti?
//        Need to compile LLVM with RTTI support
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

// FIXME: copied from rchk
bool sourceLocation(const Instruction *in, std::string& path, unsigned& line) {
  if (!in) {
    return false;
  }
  const DebugLoc& debugLoc = in->getDebugLoc();
  
  if (!debugLoc) {
    path = "/unknown";
    line = 0;
    return false;
  }

  line = debugLoc.getLine();  
  if (DIScope *scope = dyn_cast<DIScope>(debugLoc.getScope())) {
    if (sys::path::is_absolute(scope->getFilename())) {
      path = scope->getFilename().str();
    } else {
      path = scope->getDirectory().str() + "/" + scope->getFilename().str();
    }
  }
  return true;
}

// FIXME: copied from rchk
std::string sourceLocation(const Instruction *in) {
  unsigned line;
  std::string path;
  
  if (!sourceLocation(in, path, line)) {
    return "<unknown location>";
  } else {
    return path + ":" + std::to_string(line);
  }
}

// FIXME: copied from rchk
std::string funLocation(const Function *f) {
  const Instruction *instWithDI = NULL;
  for(Function::const_iterator bb = f->begin(), bbe = f->end(); !instWithDI && bb != bbe; ++bb) {
    for(BasicBlock::const_iterator in = bb->begin(), ine = bb->end(); !instWithDI && in != ine; ++in) {
      if (in->getDebugLoc()) {
        instWithDI = &*in;
      }
    }
  }
  return sourceLocation(instWithDI);
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
    errs() << analyzeDoFunction(m->getFunction("do_debug")).str() << "\n";
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
        ArgNamesTy argNames;
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
        
        errs() << nfo.str() << " " << dumpFunctionArities(uniqueFunctionArities(fun, funtab), nfo.effectiveArity) << 
          (e.isSpecial() ? " SPECIAL" : " BUILTIN") << " " << (e.isPrimitive() ? "PRIMITIVE" : "INTERNAL"); 
          
        if (1) {
          if (!e.isPrimitive()) {
            if (mayCall(fun, m->getFunction("Rf_errorcall"), m->getFunction("Rf_error"))) errs() << "!!!errorcall";
          } else {
            if (mayCall(fun, m->getFunction("Rf_error"), m->getFunction("Rf_errorcall"))) errs() << "!!!error";
          }
        }
        errs() << " " << funLocation(fun) << "\n";
        
        if (0) {
          ResolvedListAccessesTy& listAccesses = nfo.listAccesses;
          for(ResolvedListAccessesTy::const_iterator li = listAccesses.begin(), le = listAccesses.end(); li != le; ++li) {
            ListAccess& la = const_cast<ListAccess&>(li->first);
            unsigned aindex = li->second;
              errs() << "    " << la.str() << "  arg " << std::to_string(aindex) << "\n";
          }
        }
      }
    }
  }

  return 0;
}
