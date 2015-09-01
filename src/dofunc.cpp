
/* analysis of do_XXX functions */

#include "dofunc.h"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>

#include <llvm/Support/raw_ostream.h>

#include <unordered_map>

#undef NDEBUG
#include <assert.h>

using namespace llvm;

const bool DEBUG = false;

enum ArgValueState {

  AVS_UNKNOWN = 0,
  AVS_ADDRESS_TAKEN,
  AVS_CALL,
  AVS_OP,
  AVS_ARGS,
  AVS_ENV
};


typedef std::unordered_map<Value*, ArgValueState> ArgValueMapTy;

ArgValueState getAVS(ArgValueMapTy& map, Value *value) {
  auto vfind = map.find(value);
  if (vfind != map.end()) {
    return vfind->second;
  }
  return AVS_UNKNOWN;
  
  // FIXME: perhaps we could use just map[value] and take advantage of that
  //        AVS_UNKNOWN is represented as 0; but would that be really
  //        correct?
}

// check if the function calls checkArity (in the entry basic block)
//
// do_XXX(SEXP call, SEXP op, SEXP args, SEXP env)
//   
//   checkArity(op, args) -> Rf_checkArity(op, args, call)
// 
// Note that looking just at the entry block makes it unnecessary to check
// for returns from the function.  A more general approach would look at
// checkArity on all paths returning from the function, possibly spanning
// across multiple basic blocks.  It seems that checkArity should be in the
// entry basic block anyway, for code clarity.

bool ensuresArity(Function *fun) {
  
  if (DEBUG) errs() << "ensuresArity: " << fun->getName() << "\n";
  
  BasicBlock *bb = &fun->getEntryBlock();
  
  ArgValueMapTy map; // for each value, remember which argument it holds
  
  unsigned nargs = fun->arg_size();
  assert(nargs == 4);
  Function::arg_iterator ai = fun->arg_begin();

  Argument *callArg = ai++;
  Argument *opArg = ai++;
  Argument *argsArg = ai++;
  Argument *envArg = ai++;
  
  map.insert({callArg, AVS_CALL});
  map.insert({opArg, AVS_OP});
  map.insert({argsArg, AVS_ARGS});
  map.insert({envArg, AVS_ENV});
  
  for(BasicBlock::iterator ii = bb->begin(), ie = bb->end(); ii != ie; ++ii) {
    Instruction *in = ii;
    
    CallSite cs(in);
    if (cs) {
      Function *tgt = cs.getCalledFunction();
      if (tgt && tgt->getName() == "Rf_checkArityCall") { // call to checkArity
      
        assert(cs.arg_size() == 3);
        
        if (DEBUG) errs() << "Call to checkArity: " << std::to_string(getAVS(map, cs.getArgument(0))) << " "
          << std::to_string(getAVS(map, cs.getArgument(1))) << " "
          << std::to_string(getAVS(map, cs.getArgument(2))) << "\n";
        
        if (getAVS(map, cs.getArgument(0)) == AVS_OP &&
          getAVS(map, cs.getArgument(1)) == AVS_ARGS &&
          getAVS(map, cs.getArgument(2)) == AVS_CALL) {
          
          return true;
        }
      }
    }
    
    if (LoadInst* li = dyn_cast<LoadInst>(in)) { // load of a variable
      map[li] = getAVS(map, li->getPointerOperand());
      if (DEBUG) errs() << "Load result: " << std::to_string(map[li]) << " " << *li << "\n";
      continue;
    }
    
    if (StoreInst* si = dyn_cast<StoreInst>(in)) {
      if (AllocaInst *var = dyn_cast<AllocaInst>(si->getPointerOperand())) {
        
        if (getAVS(map, var) == AVS_ADDRESS_TAKEN) {
          continue;
        }
        ArgValueState s = getAVS(map, si->getValueOperand()); // a value operand may be an argument
        
        map[si] = s;
        map[var] = s;
        
        if (DEBUG) errs() << "Store result: " << std::to_string(map[si]) << " " << *si << " also variable " << *var << "\n";
        continue;
      }
    }
    map[in] = AVS_UNKNOWN;
    
    // detect when address of a variable is taken
    unsigned nops = in->getNumOperands();
    for(unsigned i = 0; i < nops; i++) {
      if (AllocaInst *var = dyn_cast<AllocaInst>(in->getOperand(i))) {
        map[var] = AVS_ADDRESS_TAKEN;
      }
    }
    
  }
  return false;
}
