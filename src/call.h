#ifndef RENT_CALL_H
#define RENT_CALL_H

#include <llvm/IR/Function.h>

using namespace llvm;

bool mayCall(Function *src, Function *tgt, Function *ign);

#endif
