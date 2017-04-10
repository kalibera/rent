
#include "call.h"

#include <llvm/IR/CallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>

#include <llvm/Support/raw_ostream.h>

#include <unordered_set>

using namespace llvm;

const bool DEBUG = false;

typedef std::unordered_set<Function*> FunctionSetTy;

bool mayCall(Function *src, Function *tgt, Function *ign, FunctionSetTy& analyzed) {
  if (analyzed.find(src) != analyzed.end()) return false;
  analyzed.insert(src);
  
  if (src == tgt || src == ign) return false; // do not analyze tgt further
  
  for(Function::iterator bb = src->begin(), bbe = src->end(); bb != bbe; ++bb) {
    for(BasicBlock::iterator in = bb->begin(), ine = bb->end(); in != ine; ++in) {
      Value *v = &*in;
      CallSite cs(v);
      if (!cs) continue;
      Function *curtgt = cs.getCalledFunction();
      if (!curtgt) continue;
      if (curtgt == tgt || mayCall(curtgt, tgt, ign, analyzed)) {
        errs() << "  " << curtgt->getName() << " calls " << tgt->getName() << "\n";
        return true;
      }
    }
  }
  return false;
}

bool mayCall(Function *src, Function *tgt, Function *ign) {

  FunctionSetTy analyzed;
  return mayCall(src, tgt, ign, analyzed);  

}

