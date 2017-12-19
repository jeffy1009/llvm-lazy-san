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

    // check*** - Only check for existance of pointer types
    bool checkArrayTy(Type *Ty);
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

    void visitAllocaInst(AllocaInst &I);
    void visitStoreInst(StoreInst &I);
    void visitReturnInst(ReturnInst &I);

    void visitMemIntrinsic(MemIntrinsic &I);
  };
} // end anonymous namespace

bool LazySanVisitor::checkArrayTy(Type *Ty) {
  Type *ElemTy = Ty->getArrayElementType();
  if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
    return false;

  if (ElemTy->isPointerTy())
    return true;

  if (ElemTy->isArrayTy())
    return checkArrayTy(ElemTy);

  assert(ElemTy->isStructTy());
  return checkStructTy(ElemTy);
}

bool LazySanVisitor::checkStructTy(Type *Ty) {
  for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
    Type *ElemTy = Ty->getStructElementType(i);
    if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
      continue;
    if (ElemTy->isPointerTy()) {
      return true;
    } else if (ElemTy->isArrayTy()) {
      if (checkArrayTy(ElemTy))
        return true;
    } else {
      assert(ElemTy->isStructTy());
      if (checkStructTy(ElemTy))
        return true;
    }
  }
  return false;
}

bool LazySanVisitor::checkTy(Type *Ty) {
  Type *ElemTy = cast<PointerType>(Ty)->getElementType();
  if (ElemTy->isPointerTy())
    return true;

  if (ElemTy->isArrayTy())
    return checkArrayTy(ElemTy);

  if (ElemTy->isStructTy())
    return checkStructTy(ElemTy);

  assert(ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy());
  return false;
}

void LazySanVisitor::insertRefCntFunc(Instruction *InsertPos,
                                      Instruction *InsertPos2,
                                      Value *V, bool ShouldInc) {
  IRBuilder<> B(InsertPos);
  LoadInst *Before = B.CreateLoad(V);
  Value *CastBefore = B.CreateBitCast(Before,
                                      Type::getInt8PtrTy(V->getContext()));
  Value *CastV = B.CreateBitCast(V, Type::getInt8PtrTy(V->getContext()));
  // TODO: beware of uninitialized values

  if (!ShouldInc) {
    B.CreateCall(DecRC, {CastBefore, CastV});
    return;
  }

  B.SetInsertPoint(InsertPos2);
  B.SetCurrentDebugLocation(InsertPos->getDebugLoc());
  LoadInst *After = B.CreateLoad(V);
  Value *CastAfter = B.CreateBitCast(After,
                                     Type::getInt8PtrTy(V->getContext()));
  B.CreateCall(IncRC, {CastAfter, CastV});
  B.CreateCall(DecRC, {CastBefore, CastV});
}

void LazySanVisitor::handleArrayTy(Instruction *InsertPos,
                                   Instruction *InsertPos2,
                                   Value *V, Type *Ty,
                                   SmallVectorImpl<Value *> &Indices,
                                   bool ShouldInc) {
  Type *ElemTy = Ty->getArrayElementType();
  if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
    return;

  IRBuilder<> B(InsertPos);
  if (ElemTy->isPointerTy()) {
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      insertRefCntFunc(InsertPos, InsertPos2,
                       B.CreateInBoundsGEP(V, TmpIndices), ShouldInc);
    }
    return;
  } else if (ElemTy->isArrayTy()) {
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      handleArrayTy(InsertPos, InsertPos2, V, ElemTy, TmpIndices, ShouldInc);
    }
  } else {
    assert(ElemTy->isStructTy());
    for (unsigned int i = 0, e = Ty->getArrayNumElements(); i < e; ++i) {
      SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
      TmpIndices.push_back(B.getInt32(i));
      handleStructTy(InsertPos, InsertPos2, V, ElemTy, TmpIndices, ShouldInc);
    }
  }
}

void LazySanVisitor::handleStructTy(Instruction *InsertPos,
                                    Instruction *InsertPos2,
                                    Value *V, Type *Ty,
                                    SmallVectorImpl<Value *> &Indices,
                                    bool ShouldInc) {
  for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
    Type *ElemTy = Ty->getStructElementType(i);
    if (ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy())
      continue;

    IRBuilder<> B(InsertPos);
    SmallVector<Value *, 4> TmpIndices(Indices.begin(), Indices.end());
    TmpIndices.push_back(B.getInt32(i));

    if (ElemTy->isPointerTy()) {
      insertRefCntFunc(InsertPos, InsertPos2,
                       B.CreateInBoundsGEP(V, TmpIndices), ShouldInc);
    } else if (ElemTy->isArrayTy()) {
      handleArrayTy(InsertPos, InsertPos2, V, ElemTy, TmpIndices, ShouldInc);
    } else {
      assert(ElemTy->isStructTy());
      handleStructTy(InsertPos, InsertPos2, V, ElemTy, TmpIndices, ShouldInc);
    }
  }
}

void LazySanVisitor::handleTy(Instruction *InsertPos, Instruction *InsertPos2,
                              Value *V, bool ShouldInc) {
  Type *Ty = cast<PointerType>(V->getType())->getElementType();
  if (Ty->isPointerTy())
    return insertRefCntFunc(InsertPos, InsertPos2, V, ShouldInc);

  IRBuilder<> B(InsertPos);
  SmallVector<Value *, 2> Indices;
  Indices.push_back(B.getInt64(0));
  if (Ty->isArrayTy())
    return handleArrayTy(InsertPos, InsertPos2, V, Ty, Indices, ShouldInc);

  if (Ty->isStructTy())
    return handleStructTy(InsertPos, InsertPos2, V, Ty, Indices, ShouldInc);

  assert(Ty->isIntegerTy() || Ty->isFloatingPointTy());
}

void LazySanVisitor::visitAllocaInst(AllocaInst &I) {
  const DataLayout &DL = I.getModule()->getDataLayout();
  IRBuilder<> Builder(I.getNextNode());
  Type *Ty = I.getAllocatedType();
  assert(Ty->isSized());
  // TODO: not always initialize
  Builder.CreateMemSet(&I, Constant::getNullValue(Builder.getInt8Ty()),
                       DL.getTypeStoreSize(Ty), 0);
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
  // TODO: beware of uninitialized values
  LoadInst *PtrBefore = Builder.CreateLoad(I.getPointerOperand());
  Cast = Builder.CreateBitCast(PtrBefore, Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(DecRC, {Cast, Cast2});
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts)
    handleTy(&I, nullptr, AI, false);
}

void LazySanVisitor::visitMemIntrinsic(MemIntrinsic &I) {
  // const DataLayout &DL = I.getModule()->getDataLayout();
  IRBuilder<> Builder(&I);
  Value *Dest = I.getDest();
  if (!checkTy(Dest->getType()))
    return;

  if (GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(Dest)) {
    int i = 0, LastNonNull = -1;
    for (User::const_op_iterator IdxI = GEPI->idx_begin(),
           IdxE = GEPI->idx_end(); IdxI != IdxE; ++IdxI, ++i) {
      if (isa<Constant>(*IdxI) && cast<Constant>(*IdxI)->isNullValue())
        continue;
      LastNonNull = i;
    }

    assert(LastNonNull != -1); // getDest should have stripped this off
    if (LastNonNull == GEPI->getNumIndices()-1)
      goto out;

    SmallVector<Value *, 2> Indices(GEPI->idx_begin(),
                                    GEPI->idx_begin()+LastNonNull+1);
    Type *IdxTy =
      GetElementPtrInst::getIndexedType(GEPI->getSourceElementType(), Indices);
    if (!checkTy(IdxTy))
      return;

    Dest = Builder.CreateInBoundsGEP(Dest, Indices);

    // TODO: check size
    // Value *Size = I.getArgOperand(2);
    // assert(DL.getTypeStoreSize(IdxType));
  }

 out:
  if (MemSetInst *MSI = dyn_cast<MemSetInst>(&I)) {
    Value *V = MSI->getValue();
    assert(isa<ConstantInt>(V) && cast<Constant>(V)->isNullValue());
  }

  handleTy(&I, I.getNextNode(), Dest, isa<MemSetInst>(&I) ? false : true);
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
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt8PtrTy(C)}, false));
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
