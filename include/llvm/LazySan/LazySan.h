//===- LazySan.h -  -----------------------*- C++ -*-===//

#ifndef LLVM_LAZYSAN_LAZYSAN_H
#define LLVM_LAZYSAN_LAZYSAN_H

#include "llvm/Pass.h"

namespace llvm {
  class LazySan : public ModulePass {
  public:
    static char ID;

    LazySan();

    bool runOnFunction(Function &F);
    bool runOnModule(Module &M) override;
    void getAnalysisUsage(AnalysisUsage &AU) const override;
  };
}

#endif /* LLVM_LAZYSAN_LAZYSAN_H */
