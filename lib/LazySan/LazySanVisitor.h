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

  Function *DecRC, *IncRC, *IncDecRC, *IncDecRC_noinc;
  Function *ClearPtrLog, *CpyPtrLog, *CheckPtrLog, *IncPtrLog, *DecPtrLog;
  Function *DecAndClearPtrLog, *IncDecCpyPtrLog, *IncDecMovePtrLog;

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

  // handle*** - insert reference count inc/dec calls
  void insertRefCntFunc(Instruction *InsertPos, Instruction *InsertPos2,
                        Value *V, bool ShouldInc);
  void handleArrayTy(Instruction *InsertPos, Instruction *InsertPos2,
                     Value *V, Type *Ty, SmallVectorImpl<Value *> &Indices,
                     bool ShouldInc);
  void handleStructTy(Instruction *InsertPos, Instruction *InsertPos2,
                      Value *V, Type *Ty, SmallVectorImpl<Value *> &Indices,
                      bool ShouldInc);
  void handleTy(Instruction *InsertPos, Instruction *InsertPos2,
                Value *V, bool ShouldInc);

  void handleScopeEntry(IRBuilder<> &B, Value *Dest, Value *Size);
  void handleScopeExit(IRBuilder<> &B, Value *Dest, Value *Size,
                       bool Check = false);

  bool shouldInstrument(Value *V, SmallPtrSetImpl<Value *> &Visited,
                        bool LookForUnion = false);
  bool maybeHeapPtr(Value *V, SmallPtrSetImpl<Value *> &Visited);

  void handleLifetimeIntr(IntrinsicInst *I);
  void handleMemSet(CallInst *I);
  void handleMemTransfer(CallInst *I);

  // Code from DangSan
  bool isSameLoadStore(Value *ptr_addr, Value *obj_addr);
  bool isPointerOperand(Value *V);
  bool isDoublePointer(Value *V);
};

}

#endif
