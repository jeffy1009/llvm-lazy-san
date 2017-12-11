#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/LazySan/LazySan.h"

#define DEBUG_TYPE "lazy-san"

using namespace llvm;

namespace {
  class LazySanVisitor : public InstVisitor<LazySanVisitor> {
    SmallVector<AllocaInst *, 8> AllocaInsts;
    Function *DecRC;
    Function *IncRC;

  public:
    LazySanVisitor(Module &M) {
      DecRC = M.getFunction("ls_dec_refcnt");
      IncRC = M.getFunction("ls_inc_refcnt");
    }

    void handlePointerTy(IRBuilder<> &B, Value *V);
    void handleArrayTy(IRBuilder<> &B, Value *V, Type *Ty,
                       SmallVectorImpl<Value *> &Indices);
    void handleStructTy(IRBuilder<> &B, Value *V, Type *Ty,
                        SmallVectorImpl<Value *> &Indices);

    void visitAllocaInst(AllocaInst &I);
    void visitStoreInst(StoreInst &I);
    void visitReturnInst(ReturnInst &I);
  };
} // end anonymous namespace

void LazySanVisitor::handlePointerTy(IRBuilder<> &B, Value *V) {
  LoadInst *Ptr = B.CreateLoad(V);
  Value *Cast = B.CreateBitCast(Ptr, Type::getInt8PtrTy(V->getContext()));
  B.CreateCall(DecRC, {Cast});
}

void LazySanVisitor::handleArrayTy(IRBuilder<> &B, Value *V, Type *Ty,
                                   SmallVectorImpl<Value *> &Indices) {
  Type *ElemTy = Ty->getArrayElementType();
  if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
    return;

  if (ElemTy->isPointerTy()) {
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      handlePointerTy(B, B.CreateInBoundsGEP(V, TmpIndices));
    }
    return;
  } else if (ElemTy->isArrayTy()) {
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      handleArrayTy(B, V, ElemTy, TmpIndices);
    }
  } else {
    assert(ElemTy->isStructTy());
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      handleStructTy(B, V, ElemTy, TmpIndices);
    }
  }
}

void LazySanVisitor::handleStructTy(IRBuilder<> &B, Value *V, Type *Ty,
                                    SmallVectorImpl<Value *> &Indices) {
  for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
    Type *ElemTy = Ty->getStructElementType(i);
    if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
      continue;

    SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
    TmpIndices.push_back(B.getInt32(i));

    if (ElemTy->isPointerTy()) {
      handlePointerTy(B, B.CreateInBoundsGEP(V, TmpIndices));
    } else if (ElemTy->isArrayTy()) {
      handleArrayTy(B, V, ElemTy, TmpIndices);
    } else {
      assert(ElemTy->isStructTy());
      handleStructTy(B, V, ElemTy, TmpIndices);
    }
  }
}

void LazySanVisitor::visitAllocaInst(AllocaInst &I) {
  AllocaInsts.push_back(&I);
}

void LazySanVisitor::visitStoreInst(StoreInst &I) {
  Value *Ptr = I.getValueOperand();
  Type *Ty = Ptr->getType();
  if (!Ty->isPointerTy())
    return;

  IRBuilder<> Builder(&I);

  // NOTE: we should increase refcnt before decreasing it..
  // if it is decreased first, refcnt could become 0 and the quarantine cleared
  // but if the pointer happens to point to the same object, refcnt will become
  // one again..

  // increase ref count
  // mark field as pointer type
  Value *Cast = Builder.CreateBitCast(Ptr, Type::getInt8PtrTy(I.getContext()));
  Value *Cast2 = Builder.CreateBitCast(I.getPointerOperand(),
                                       Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(IncRC, {Cast, Cast2});

  // decrease ref count
  LoadInst *PtrBefore = Builder.CreateLoad(I.getPointerOperand());
  Cast = Builder.CreateBitCast(PtrBefore, Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(DecRC, {Cast});
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts) {
    Type *Ty = AI->getAllocatedType();
    if (Ty->isPointerTy()) {
      handlePointerTy(Builder, AI);
      continue;
    }

    SmallVector<Value *, 2> Indices;
    Indices.push_back(Builder.getInt32(0));
    if (Ty->isStructTy()) {
      handleStructTy(Builder, AI, Ty, Indices);
      continue;
    }

    if (Ty->isArrayTy())
      handleArrayTy(Builder, AI, Ty, Indices);
  }
}

char LazySan::ID = 0;

static RegisterPass<LazySan> X("lazy-san", "Lazy Pointer Sanitizer Pass");

bool LazySan::runOnFunction(Function &F) {
  LazySanVisitor LSV(*F.getParent());
  LSV.visit(F);

  // To force linking
  if (F.getName().startswith("abcdef")) {
    F.viewCFGOnly();
    F.viewCFG();
  }

  return true;
}

bool LazySan::runOnModule(Module &M) {
  LLVMContext &C = M.getContext();
  M.getOrInsertFunction("ls_dec_refcnt",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C)}));
  M.getOrInsertFunction("ls_inc_refcnt",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt8PtrTy(C)}, false));
  dbgs() << "Hello World!!!\n";
  for (Function &F : M.functions()) {
    if (F.empty())
      continue;

    runOnFunction(F);
  }

  return true;
}

void LazySan::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
}
