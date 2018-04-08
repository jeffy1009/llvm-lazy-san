#ifndef LLVM_LAZYSAN_LAZYSANVISITOR_H
#define LLVM_LAZYSAN_LAZYSANVISITOR_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

namespace llvm {

class LazySanVisitor : public InstVisitor<LazySanVisitor> {
  const EQTDDataStructures *DSA;
  AliasAnalysis *AA;
  DominatorTree *DT;
  LoopInfo *LI;

  DenseMap<AllocaInst *, Value *> DynamicAllocaSizeMap;
  // allocas to be processed at return
  SmallVector<AllocaInst *, 16> AllocaInsts;
  // allocas to be checked when -enable-check is on
  SmallVector<AllocaInst *, 16> AllocaInstsCheck;

  Function *IncDecRC, *IncDecRC_noinc;
  Function *CheckPtrLog, *DecPtrLog, *DecPtrLogAddr;
  Function *IncDecCpyPtrLog, *IncDecMovePtrLog;

  bool HandleDynamicAlloca;

 public:
  LazySanVisitor(Module &M, const EQTDDataStructures *dsa, AliasAnalysis *aa,
                 DominatorTree *dt, LoopInfo *li);

  void visitAllocaInst(AllocaInst &I);
  void visitStoreInst(StoreInst &I);

  void visitCallSite(CallSite CS);
  void visitReturnInst(ReturnInst &I);

 private:
  // check*** - Only check for existance of pointer types
  bool checkArrayTy(Type *Ty, bool IgnoreI8 = false);
  bool checkStructTy(Type *Ty);
  bool checkTy(Type *Ty);

  void handleScopeExit(IRBuilder<> &B, Value *Dest, Value *Size,
                       bool Check = false);

  bool isCastFromPtr(Value *V, SmallPtrSetImpl<Value *> &Visited,
                     bool LookForDoublePtr);
  bool shouldInstrument(Value *V, SmallPtrSetImpl<Value *> &Visited,
                        bool LookForUnion, bool LookForDoublePtr,
                        bool TrackI8);
  bool maybeHeapPtr(Value *V, SmallPtrSetImpl<Value *> &Visited);

  void handleLifetimeIntr(IntrinsicInst *I);
  void handleMemSet(CallInst *I);
  void handleMemTransfer(CallInst *I);
};

}

#endif
