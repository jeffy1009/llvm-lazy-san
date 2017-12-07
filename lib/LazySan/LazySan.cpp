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

  public:
    LazySanVisitor() {}

    void visitAllocaInst(AllocaInst &I);
    void visitStoreInst(StoreInst &I);
    void visitReturnInst(ReturnInst &I);
  };
} // end anonymous namespace

void LazySanVisitor::visitAllocaInst(AllocaInst &I) {
  AllocaInsts.push_back(&I);
}

void LazySanVisitor::visitStoreInst(StoreInst &I) {
  Value *Ptr = I.getValueOperand();
  Type *Ty = Ptr->getType();
  if (!Ty->isPointerTy())
    return;

  Function *DecRC = I.getModule()->getFunction("ls_dec_refcnt");
  Function *IncRC = I.getModule()->getFunction("ls_inc_refcnt");

  IRBuilder<> Builder(&I);

  // NOTE: we should increase refcnt before decreasing it..
  // if it is decreased first, refcnt could become 0 and the quarantine cleared
  // but if the pointer happens to point to the same object, refcnt will become
  // one again..

  // increase ref count
  Value *Cast = Builder.CreateBitCast(Ptr, Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(IncRC, {Cast});

  // decrease ref count
  LoadInst *PtrBefore = Builder.CreateLoad(I.getPointerOperand());
  Cast = Builder.CreateBitCast(PtrBefore, Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(DecRC, {Cast});
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  Function *DecRC = I.getModule()->getFunction("ls_dec_refcnt");

  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts) {
    Type *Ty = AI->getAllocatedType();
    if (Ty->isPointerTy()) {
      LoadInst *Ptr = Builder.CreateLoad(AI);
      Value *Cast = Builder.CreateBitCast(Ptr, Type::getInt8PtrTy(I.getContext()));
      Builder.CreateCall(DecRC, {Cast});
      continue;
    }

    if (Ty->isStructTy()) {
      for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
        Type *ElemTy = Ty->getStructElementType(i);
        if (ElemTy->isPointerTy()) {
          assert(0);
          continue;
        }

        if (ElemTy->isArrayTy()) {
          ElemTy = ElemTy->getArrayElementType();
          assert(ElemTy->isIntegerTy());
          continue;
        }

        assert(ElemTy->isIntegerTy());
      }
    }

    if (Ty->isArrayTy()) {
      Type *ElemTy = Ty->getArrayElementType();
      assert(ElemTy->isIntegerTy());
    }
  }
}

char LazySan::ID = 0;

static RegisterPass<LazySan> X("lazy-san", "Lazy Pointer Sanitizer Pass");

bool LazySan::runOnFunction(Function &F) {
  LazySanVisitor LSV;
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
                                          {Type::getInt8PtrTy(C)}));
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
