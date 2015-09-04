
/* analysis of do_XXX functions */

#include "dofunc.h"

#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Module.h>

#include <llvm/Support/raw_ostream.h>

#include <unordered_map>
#include <unordered_set>
#include <vector>

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

enum ValueStateKind {
  VSK_CALL = 0,
  VSK_OP,
  VSK_ARGS,
  VSK_ENV,
  VSK_ARGCNT, /* just to have a macro for 4 - the number of watched arguments */
  
  VSK_UNKNOWN
};

enum ArgValueKind {
  AVK_CAR = 0, // pointer into an args cell to the CAR field
  AVK_CDR,     //                                  CDR
  AVK_TAG,     //                                  TAG
  AVK_HEADER,  // pointer to beginning of the args cell (start of header)
  AVK_NA       // N/A (not a value related to args)
  
  // currently AVK_CDR is a pointer to the location where the pointer to the header of the list is stored
  // AVK_HEADER is a pointer to where the list is stored
  // so, the "args" argument is AVK_CDR (because it is something that has to be loaded to get to the header)
};

struct ValueState {

  ValueStateKind kind;
  ArgValueKind akind;
  int argDepth;
  
  ValueState(): kind(VSK_UNKNOWN), akind(AVK_NA), argDepth(-1) {}

  ValueState(ValueStateKind kind, ArgValueKind akind, int argDepth):
    kind(kind), akind(akind), argDepth(argDepth) {}

  ValueState(ValueStateKind kind) : ValueState(kind, AVK_NA, -1) {}
  
  bool merge(ValueState other) {
    
    if (kind == VSK_UNKNOWN) {
      return false;
    }
    
    // FIXME: this is very restrictive; it won't e.g. be able to handle loops
    if (kind != other.kind || akind != other.akind || argDepth != other.argDepth) {
      kind = VSK_UNKNOWN;
      akind = AVK_NA;
      argDepth = -1;
      return true;
    }
    
    return false;
  }
  
  bool setUnknown() {
    bool changed = false;
    
    if (kind != VSK_UNKNOWN) {
      kind = VSK_UNKNOWN;
      changed = true;
    }
    
    if (akind != AVK_NA) {
      akind = AVK_NA;
      changed = true;
    }
    
    if (argDepth != -1) {
      argDepth = -1;
      changed = true;
    }
    
    return changed;
  }
  
  bool operator==(const ValueState& other) const {
    if (kind != other.kind) {
      return false;
    }
    if (kind == VSK_ARGS) {
      return akind == other.akind && argDepth == other.argDepth;
    }
    return true;
  }
};

typedef std::unordered_map<Value*, ValueState> ValuesMapTy;

// from Boost
template <class T>
inline void hash_combine(std::size_t& seed, const T& v) {
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

struct BlockState {

  BasicBlock *bb;
  ValuesMapTy vmap;
  bool checkArityCalled; // check arity _definitely_ called
  mutable bool dirty; // not included in equals, hash
  size_t hashcode;
  
  BlockState(BasicBlock *bb, bool dirty): vmap(), checkArityCalled(false), dirty(dirty), hashcode(0) {};
  BlockState(BasicBlock *bb, BlockState& other, bool dirty): bb(bb), vmap(other.vmap), checkArityCalled(other.checkArityCalled), dirty(dirty) {};
  
  bool merge(const BlockState& other) {

    bool changed = false;

    if (checkArityCalled && !other.checkArityCalled) {
      checkArityCalled = false;
      changed = true;
    }
    for(ValuesMapTy::iterator mi = vmap.begin(), me = vmap.end(); mi != me; ++mi) {
      
      Value* value = mi->first;
      ValueState& thisState = mi->second;
      
      auto vsearch = other.vmap.find(value);
      if (vsearch == other.vmap.end()) {
        if (thisState.setUnknown()) {
          changed = true;
        }
      } else {
        ValueState otherState = vsearch->second;
        if (thisState.merge(otherState)) {
          changed = true;
        }
      }
    }
    // NOTE: states in other.vmap that are not in vmap can be ignored, because
    //   since they are not in vmap, they are to be merged wth unknown state
    return changed;
  }
  
  void hash() {
    size_t res;
    hash_combine(res, checkArityCalled);    
    hash_combine(res, vmap.size());
    for(ValuesMapTy::iterator vi = vmap.begin(), ve = vmap.end(); vi != ve; ++vi) {
      Value *val = vi->first;
      ValueState& vs = vi->second;
      
      hash_combine(res, val);
      hash_combine(res, (char) vs.kind);
      if (vs.kind == VSK_ARGS) {
        hash_combine(res, (char) vs.akind);
        hash_combine(res, vs.argDepth);
      }
    }
    hashcode = res;
  }
  
  void dump() {
    errs() << "    ===== block state =====\n";
    errs() << "    checkArityCalled=" << std::to_string(checkArityCalled) << "\n";
    for(ValuesMapTy::iterator vi = vmap.begin(), ve = vmap.end(); vi != ve; ++vi) {
      Value *val = vi->first;
      ValueState vs = vi->second;
      
      if (vs.kind == VSK_UNKNOWN) {
        continue;
      }
      
      errs() << "      ";
      switch(vs.kind) {
        case VSK_ARGS:
          errs() << "ARGS depth=" << std::to_string(vs.argDepth) << " ";
          switch (vs.akind) {
            case AVK_CAR: errs() << "CAR"; break;
            case AVK_CDR: errs() << "CDR"; break;
            case AVK_TAG: errs() << "TAG"; break;
            case AVK_HEADER: errs() << "HEADER"; break;
            case AVK_NA: errs() << "NA"; break;
          }
          break;
        case VSK_CALL: errs() << "CALL"; break;
        case VSK_OP: errs() << "OP"; break;
        case VSK_ENV: errs() << "ENV"; break;
      }
      errs() << " " << *val << "\n";
    }
    errs() << "\n";
  }
};

// WARNING: excludes dirty flag and basic block!
struct BlockState_equal {
  bool operator() (const BlockState& lhs, const BlockState& rhs) const {
    // do not compare dirty flag
    return lhs.hashcode == rhs.hashcode && lhs.vmap == rhs.vmap && lhs.checkArityCalled == rhs.checkArityCalled;
  }
};

struct BlockState_hash {
  size_t operator()(const BlockState& t) const {
    return t.hashcode;
  }
};

typedef std::unordered_set<BlockState, BlockState_hash, BlockState_equal> BlockStatesSetTy; // allow multiple states for a basic block for adaptive merging
typedef std::unordered_map<BasicBlock*, BlockStatesSetTy> BlockStatesMapTy;
typedef std::vector<BasicBlock*> BlocksVectorTy; // FIXME: should the worklist have pointers to states?

ValueState getVS(ValuesMapTy& vmap, Value *v) {

  auto vsearch = vmap.find(v);
  if (vsearch == vmap.end()) {
    return ValueState();
  } else {
    return vsearch->second;
  }
}

// FIXME: should also support integers, integer guards, length of the arg list, related guards on nil value
DoFunctionInfo analyzeDoFunction(Function *fun) {

  unsigned maxStatesPerBlock = 20; // FIXME: make this depend on expected arity (or arity specified in FunTab)

  GlobalVariable *nilValue = fun->getParent()->getGlobalVariable("R_NilValue", true);
  assert(nilValue != NULL);

  // FIXME: verify it is a do_XXX function
  
  BlocksVectorTy workList;
  BlockStatesMapTy states;
  
  // set up the initial state
  BasicBlock *eb = &fun->getEntryBlock();
  workList.push_back(eb);
  BlockState ebs(eb, true /* dirty */);
  ValuesMapTy& evmap = ebs.vmap;
  
  unsigned nargs = fun->arg_size();
  assert(nargs == 4);
  Function::arg_iterator ai = fun->arg_begin();

  Argument *callArg = ai++;
  Argument *opArg = ai++;
  Argument *argsArg = ai++;
  Argument *envArg = ai++;
  
  evmap.insert({callArg, ValueState(VSK_CALL)});
  evmap.insert({opArg, ValueState(VSK_OP)});
  evmap.insert({argsArg, ValueState(VSK_ARGS, AVK_CDR, -1)});
    // depth -1 means that on load, the pointer will get depth 0, which is what we want
  evmap.insert({envArg, ValueState(VSK_ENV)});
  ebs.hash();
  
  states.insert({eb, {ebs}});

  // prepare results
  DoFunctionInfo res(fun);  
  res.checkArityCalled = true; // this has a rather iffy semantics
  res.usesTags = false;
  res.computesArgsLength = false;
  res.effectiveArity = 0;
  res.complexUseOfOp = false;
  res.complexUseOfArgs = false;
  res.complexUseOfCall = false;
  res.complexUseOfEnv = false;
  
  if (DEBUG) errs() << "adf: analyzing " << fun->getName() << "\n";
  
  // work-list forward flow analysis (with optional merging/state matching)
  while(!workList.empty()) {
    BasicBlock *bb = workList.back();
    workList.pop_back();
    
    // take the first dirty state from the given block
    BlockStatesSetTy& bs = states.at(bb);
    BlockStatesSetTy::iterator bsi = bs.begin(), bse = bs.end();
    while(bsi != bse && !bsi->dirty) ++bsi;
    if (bsi == bse) {
      // no dirty block state
      // this can happen in case of adaptive merging
      continue;
    }
    bsi->dirty = false;
    
    BlockState s = *bsi; // copy
    ValuesMapTy& vmap = s.vmap;
    
    if (DEBUG) errs() << "adf: analyzing basic block " << *bb << "\n";
    if (DEBUG) s.dump();
    
    for(BasicBlock::iterator ii = bb->begin(), ie = bb->end(); ii != ie; ++ii) {
      Instruction *in = ii;

      // TODO: add support for *LENGTH, *length or args, and hence also integer guards
      // TODO: add support for address taken
      // NOTE: I could relative easily detect unused arguments
      
      if (DEBUG) errs() << "adf: analyzing instruction " << *in << "\n";
      
      CallSite cs(in);
      if (cs) {
        Function *tgt = cs.getCalledFunction();
        if (tgt && tgt->getName() == "Rf_checkArityCall") { // call to checkArity
      
          assert(cs.arg_size() == 3);
          
          ValueState vsOp = getVS(vmap, cs.getArgument(0));
          ValueState vsArgs = getVS(vmap, cs.getArgument(1));
          ValueState vsCall = getVS(vmap, cs.getArgument(2));
          
          if (vsOp.kind == VSK_OP && vsCall.kind == VSK_CALL && vsArgs.kind == VSK_ARGS &&
            vsArgs.akind == AVK_HEADER && vsArgs.argDepth == 0) {
            
            s.checkArityCalled = true;
            if (DEBUG) errs() << "   adf: -> checkArityCalled " << *in << "\n";
            continue;
          }
        }
        if (tgt && (tgt->getName() == "Rf_length" || tgt->getName() == "Rf_xlength")) {

          // FIXME: we probably will have to model an integer that represents the arg length
          assert(cs.arg_size() == 1);
          
          ValueState vs = getVS(vmap, cs.getArgument(0));
          if (vs.kind == VSK_ARGS && vs.akind == AVK_HEADER) {
            res.computesArgsLength = true;
            if (DEBUG) errs() << "   adf: -> computesArgsLength " << *in << "\n";
            continue;
          }
        }
        if (tgt && (tgt->getName() == "Rf_protect" || tgt->getName() == "Rf_ProtectWithIndex" || tgt->getName() == "Rf_PreserveObject")) {
          assert(cs.arg_size() > 0);
          
          ValueState vs = getVS(vmap, cs.getArgument(0));
          if (vs.kind == VSK_ARGS && vs.akind == AVK_HEADER) {
            if (DEBUG) errs() << "   adf: -> protects arguments (which is usually unnecessary) " << *in << "\n";  
            continue;
          }
        }
      } // handled call

      if (LoadInst* li = dyn_cast<LoadInst>(in)) { // load of a variable
        ValueState vs = getVS(vmap, li->getPointerOperand());
        
        if (vs.kind == VSK_ARGS) {
          switch(vs.akind) {
            case AVK_TAG:
              res.usesTags = true;
              if (DEBUG) errs() << "   adf: -> TAG load" << *in << "\n";
              break;
            case AVK_CAR:
              if (vs.argDepth >= 0 && vs.argDepth + 1 > res.effectiveArity) {
                res.effectiveArity = vs.argDepth + 1;
              }
              if (DEBUG) errs() << "   adf: -> CAR load (effective arity now " << std::to_string(res.effectiveArity)  << ") " << *in << "\n";
              break;
            case AVK_CDR:
              vs.argDepth++; // the default vs.argDepth of -1 becomes 0
              vs.akind = AVK_HEADER;
              vmap[li] = vs;
              if (DEBUG) errs() << "   adf: -> CDR load (depth now " << std::to_string(vs.argDepth)  << ") " << *in << "\n";
              break;
            case AVK_HEADER:
              res.complexUseOfArgs = true;
              if (DEBUG) errs() << "   adf: -> HEADER load, error?" << *in << "\n";
              break;
          }
          continue;
        } // handled loading of VSK_ARGS
        
        if (vs.kind != VSK_UNKNOWN) {
          vmap[li] = vs;
          if (DEBUG) errs() << "   adf: -> known value kind load " << *in << "\n";
        }
        continue;
      } // handled load

      if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(in)) {
        if (gep && gep->isInBounds() && gep->getNumIndices() == 2 && gep->hasAllConstantIndices() &&
          cast<ConstantInt>(gep->getOperand(1))->isZero() && cast<ConstantInt>(gep->getOperand(2))->getZExtValue() == 4) {
          
            // skipping the header of args
            ValueState vs = getVS(vmap, gep->getOperand(0));
            if (vs.kind == VSK_ARGS && vs.akind == AVK_HEADER) {

              // handle CAR(x), CDR(x), TAG(x)
              //   this is implemented through looking forward to user instructions
              //   and supporting only certain code patterns
              
              //  %5 = load %struct.SEXPREC** %3, align 8, !dbg !68685 ; [#uses=1 type=%struct.SEXPREC*] [debug line = 754:20]
              //  %6 = getelementptr inbounds %struct.SEXPREC* %5, i32 0, i32 4, !dbg !68685 ; [#uses=1 type=%union.anon*] [debug line = 754:20] <==== skip header (4 bytes)
              //        <=== first index is 0 (not an array of structures, just pointer to structure)
              //        <=== second index is 4 -- we want the 5th item of the structure (which is the anonymous union) ... so to skip the header
              //                    
              // %7 = bitcast %union.anon* %6 to %struct.symsxp_struct*, !dbg !68685 ; [#uses=1 type=%struct.symsxp_struct*] [debug line = 754:20]
              // %8 = getelementptr inbounds %struct.symsxp_struct* %7, i32 0, i32 0, !dbg !68685 ; [#uses=1 type=%struct.SEXPREC**] [debug line = 754:20]
              //        <=== first index is 0 (only one union)
              //	<=== second index is 0 - the first element of the union is "carval"
                                                      

              // FIXME: avoid copy-paste in recovery code (turn into function?)
              // the bitcast
              if (!gep->hasOneUse()) {
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              BitCastInst *bc = dyn_cast<BitCastInst>(gep->user_back());
              PointerType *ty = dyn_cast<PointerType>(bc->getDestTy());
              if (!ty) {
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              StructType *sty = dyn_cast<StructType>(ty->getElementType());
              if (!sty || !sty->hasName() || sty->getName() != "struct.symsxp_struct") {
                // FIXME: it is rather odd that clang happens to generate bitcast to symsxp_struct, even though the list
                // is represented by listsxp_struct; it would be more correct to work with offsets from the head
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              
              // the second getelementptr
              if (!bc->hasOneUse()) {
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              gep = dyn_cast<GetElementPtrInst>(bc->user_back());
              if (!gep || !gep->isInBounds() || gep->getNumIndices() != 2 || !gep->hasAllConstantIndices()) {
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              if (!cast<ConstantInt>(gep->getOperand(1))->isZero()) {
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              unsigned idx = cast<ConstantInt>(gep->getOperand(2))->getZExtValue();
              if (idx > 2) {
                // should not happen given in bounds
                res.complexUseOfArgs = true;
                if (DEBUG) errs() << "   adf: -> complex use of args (unsupported load of cell header) " << *in << "\n";
                continue;
              }
              switch(idx) {
                case 0: vs.akind = AVK_CAR; break;
                case 1: vs.akind = AVK_CDR; break;
                case 2: vs.akind = AVK_TAG; break;
              }
              vmap[gep] = vs; // NOTE: we are here setting state of the GEP, the values in between will stay "unknown"
              if (DEBUG) errs() << "   adf: -> CAR/CDR/TAG operation (depth now " << std::to_string(vs.argDepth)  << ") " << *in << "\n";
              continue;      
            }
          }
      } // handled get-element-pointer

      if (StoreInst* si = dyn_cast<StoreInst>(in)) {
        if (AllocaInst *var = dyn_cast<AllocaInst>(si->getPointerOperand())) {
        
          ValueState vs = getVS(vmap, si->getValueOperand());
          if (vs.kind != VSK_UNKNOWN) {
            vmap[si] = vs;
            vmap[var] = vs;
            if (DEBUG) errs() << "   adf: -> store operation with known value state " << *in << "\n";
          }
        }
        continue;
      } // handled store
      
      if (CmpInst* ci = dyn_cast<CmpInst>(in)) {

        LoadInst *l1 = dyn_cast<LoadInst>(ci->getOperand(0));
        LoadInst *l2 = dyn_cast<LoadInst>(ci->getOperand(1));
        
        if (l1 && l2) {
          Value *arg = NULL;
          if (l1->getPointerOperand() == nilValue) {
            arg = ci->getOperand(1);
          } else if (l2->getPointerOperand() == nilValue) {
            arg = ci->getOperand(0);
          }
        
          if (arg) {
            ValueState vs = getVS(vmap, arg);
            if (vs.kind == VSK_ARGS && vs.akind == AVK_HEADER) {
              res.computesArgsLength = true;
              if (DEBUG) errs() << "   adf: -> computesArgsLength " << *in << "\n";
              continue;
            }
          }
        }
      } // handled compare
      
      // detect when address of a variable is taken (and all other unsupported uses)
      unsigned nops = in->getNumOperands();
      for(unsigned i = 0; i < nops; i++) {
        Value *val = in->getOperand(i);
        ValueState vs = getVS(vmap, val);
        if (DEBUG && vs.kind != VSK_UNKNOWN) errs() << "   adf: -> complex use of do_function argument " << *in << "\n";
        switch(vs.kind) {
          case VSK_CALL: res.complexUseOfCall = true; break;
          case VSK_OP: res.complexUseOfOp = true; break;
          case VSK_ENV: res.complexUseOfEnv = true; break;
          case VSK_ARGS:
            switch(vs.akind) {
              // FIXME: I am in fact not detecting changes of the arg list
              case AVK_HEADER:
              case AVK_CDR:
                res.complexUseOfArgs = true; break;
              case AVK_TAG:
                res.usesTags = true; break;
            }
            break;
        }
        if (vs.kind != VSK_UNKNOWN) {
          vmap.erase(val); // mark var as unknown
        }
      }
      // leave vmap[in] as unknown
    }
    
    TerminatorInst *t = bb->getTerminator();
    if (isa<ReturnInst>(t) || isa<UnreachableInst>(t)) {
      if (!s.checkArityCalled) {
        if (DEBUG) errs() << "   adf: -> check arity missed on this path " << *t << "\n";
        res.checkArityCalled = false;
      }
    }
    unsigned nsucc = t->getNumSuccessors();
    for(unsigned i = 0; i < nsucc; i++) {
      BasicBlock *sbb = t->getSuccessor(i);
      BlockState news(sbb, s, true /* dirty */);
      
      auto bsearch = states.find(sbb);
      if (bsearch == states.end()) {
        // no state for this basic block yet
        news.hash();
        states.insert({sbb, {news}});
        workList.push_back(sbb);
        if (DEBUG) errs() << "   adf: -> added successor to new block " << *t << "\n";
        continue;
      }
      BlockStatesSetTy &bs = bsearch->second;
      
      auto ssearch = bs.find(news); // ignores dirty
      if (ssearch != bs.end()) {
        // the state is already known and handled
        if (DEBUG) errs() << "   adf: -> found already explored successor state " << *t << "\n";
        continue;
      }
      
      if (bs.size() >= maxStatesPerBlock) {

        // merge all states
        for(BlockStatesSetTy::iterator si = bs.begin(), se = bs.end(); si != se; ++si) {
          const BlockState& os = *si;
          news.merge(os); // ignores dirty
        }
        bs.clear();
        if (DEBUG) errs() << "   adf: -> merged successor states into a single one " << *t << "\n";
      }
      
      if (DEBUG) errs() << "   adf: -> added successor state to known block " << *t << "\n";
      news.hash();
      bs.insert(news);
      workList.push_back(sbb);
    }
  }
  return res;
}
