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
    // allocas to be processed at return
    SmallVector<AllocaInst *, 16> AllocaInsts;

    Function *DecRC, *IncRC;
    Function *ClearPtrLog, *CpyPtrLog, *IncPtrLog, *DecPtrLog;

  public:
    LazySanVisitor(Module &M) {
      DecRC = M.getFunction("ls_dec_refcnt");
      IncRC = M.getFunction("ls_inc_refcnt");
      ClearPtrLog = M.getFunction("ls_clear_ptrlog");
      CpyPtrLog = M.getFunction("ls_copy_ptrlog");
      IncPtrLog = M.getFunction("ls_inc_ptrlog");
      DecPtrLog = M.getFunction("ls_dec_ptrlog");
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

    void handleScopeEntry(IRBuilder<> &B, Value *Dest, Value *Size);
    void handleScopeExit(IRBuilder<> &B, Value *Dest, Value *Size);

    void visitAllocaInst(AllocaInst &I);
    void visitStoreInst(StoreInst &I);

    void handleLifetimeIntr(IntrinsicInst *I);
    void visitCallInst(CallInst &I);
    void visitReturnInst(ReturnInst &I);
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

// Code copied from lib/Transforms/Utils/InlineFunction.cpp
// Check whether this Value is used by a lifetime intrinsic.
static bool isUsedByLifetimeMarker(Value *V) {
  for (User *U : V->users()) {
    if (IntrinsicInst *II = dyn_cast<IntrinsicInst>(U)) {
      switch (II->getIntrinsicID()) {
      default: break;
      case Intrinsic::lifetime_start:
      case Intrinsic::lifetime_end:
        return true;
      }
    }
  }
  return false;
}

// Code copied from lib/Transforms/Utils/InlineFunction.cpp
// Check whether the given alloca already has
// lifetime.start or lifetime.end intrinsics.
static bool hasLifetimeMarkers(AllocaInst *AI) {
  Type *Ty = AI->getType();
  Type *Int8PtrTy = Type::getInt8PtrTy(Ty->getContext(),
                                       Ty->getPointerAddressSpace());
  if (Ty == Int8PtrTy)
    return isUsedByLifetimeMarker(AI);

  // Do a scan to find all the casts to i8*.
  for (User *U : AI->users()) {
    if (U->getType() != Int8PtrTy) continue;
    if (U->stripPointerCasts() != AI) continue;
    if (isUsedByLifetimeMarker(U))
      return true;
  }
  return false;
}

void LazySanVisitor::handleScopeEntry(IRBuilder<> &B, Value *Dest,
                                      Value *Size) {
  Value *Cast = B.CreateBitCast(Dest, Type::getInt8PtrTy(Dest->getContext()));
  // TODO: not always initialize
  B.CreateMemSet(Dest, Constant::getNullValue(B.getInt8Ty()), Size, 0);
  B.CreateCall(ClearPtrLog, {Cast, Size});
}

void LazySanVisitor::handleScopeExit(IRBuilder<> &B, Value *Dest,
                                     Value *Size) {
  Value *Cast = B.CreateBitCast(Dest, Type::getInt8PtrTy(Dest->getContext()));
  // handleTy(&I, nullptr, Dest, false);
  B.CreateCall(DecPtrLog, {Cast, Size});
}

// Code copied from lib/Transforms/Instrumentation/AddressSanitizer.cpp
static uint64_t getAllocaSizeInBytes(AllocaInst *AI) {
  Type *Ty = AI->getAllocatedType();
  uint64_t SizeInBytes =
    AI->getModule()->getDataLayout().getTypeAllocSize(Ty);
  return SizeInBytes;
}

void LazySanVisitor::visitAllocaInst(AllocaInst &I) {
  // Allocas having lifetime markders will be processed at the lifetime markers
  if (hasLifetimeMarkers(&I))
    return;

  assert(I.getParent() == &I.getFunction()->getEntryBlock()
         && "alloca not in the entry basic block!");
  assert(I.isStaticAlloca());

  IRBuilder<> Builder(I.getNextNode());
  handleScopeEntry(Builder, &I, Builder.getInt64(getAllocaSizeInBytes(&I)));
  AllocaInsts.push_back(&I);
}

void LazySanVisitor::visitStoreInst(StoreInst &I) {
  Value *Ptr = I.getValueOperand();
  Type *Ty = Ptr->getType();
  assert(!isa<PtrToIntInst>(Ptr));
  if (!Ty->isPointerTy()) {
    Value *Lhs = I.getPointerOperand();
    // Not using stripPointerCasts here. we don't want to strip all-zero GEP
    if (isa<BitCastInst>(Lhs))
      Lhs = cast<BitCastInst>(Lhs)->getOperand(0);
    assert(Lhs == Lhs->stripPointerCasts());
    PointerType *LhsTy = cast<PointerType>(Lhs->getType());
    assert(!isa<PtrToIntInst>(Lhs));
    assert(!isa<GlobalAlias>(Lhs));
    if (!checkTy(LhsTy))
      return;
  }

  IRBuilder<> Builder(&I);

  // NOTE: we should increase refcnt before decreasing it..
  // if it is decreased first, refcnt could become 0 and the quarantine cleared
  // but if the pointer happens to point to the same object, refcnt will become
  // one again..

  // increase ref count
  // mark field as pointer type
  Value *Cast = Builder.CreateBitOrPointerCast(Ptr,
                                               Type::getInt8PtrTy(I.getContext()));
  Value *Cast2 = Builder.CreateBitOrPointerCast(I.getPointerOperand(),
                                                Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(IncRC, {Cast, Cast2});

  // decrease ref count
  // TODO: beware of uninitialized values
  LoadInst *PtrBefore = Builder.CreateLoad(I.getPointerOperand());
  Cast = Builder.CreateBitOrPointerCast(PtrBefore,
                                        Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(DecRC, {Cast, Cast2});
}

void LazySanVisitor::handleLifetimeIntr(IntrinsicInst *I) {
  IRBuilder<> Builder(I);
  Value *Dest = I->getArgOperand(1)->stripPointerCasts();
  Value *Size = I->getArgOperand(0);
  if (I->getIntrinsicID() == Intrinsic::lifetime_start)
    handleScopeEntry(Builder, Dest, Size);
  else
    handleScopeExit(Builder, Dest, Size);
}

void LazySanVisitor::visitCallInst(CallInst &I) {
  // const DataLayout &DL = I.getModule()->getDataLayout();
  Module *M = I.getModule();
  Function *CalledFunc = I.getCalledFunction();
  if (!CalledFunc) // skip indirect calls
    return;

  if (IntrinsicInst *Intr = dyn_cast<IntrinsicInst>(&I)) {
    if (Intr->getIntrinsicID() == Intrinsic::lifetime_start
        || Intr->getIntrinsicID() == Intrinsic::lifetime_start)
      return handleLifetimeIntr(Intr);
  }

  if (CalledFunc->getName().equals("malloc"))
    return I.setCalledFunction(M->getFunction("malloc_wrap"));
  if (CalledFunc->getName().equals("calloc"))
    return I.setCalledFunction(M->getFunction("calloc_wrap"));
  if (CalledFunc->getName().equals("realloc"))
    return I.setCalledFunction(M->getFunction("realloc_wrap"));
  if (CalledFunc->getName().equals("free"))
    return I.setCalledFunction(M->getFunction("free_wrap"));

  if (!isa<MemIntrinsic>(&I)
      && !CalledFunc->getName().equals("memset")
      && !CalledFunc->getName().equals("memmove")
      && !CalledFunc->getName().equals("memcpy"))
    return;

  IRBuilder<> Builder(&I);
  Value *Dest = I.getArgOperand(0)->stripPointerCasts();
  // TODO: optimize when there is no pointer type
  // if (!checkTy(Dest->getType()))
  //   return;

  bool ShouldInc = true;
  if (isa<MemSetInst>(&I)
      || CalledFunc->getName().equals("memset"))
    ShouldInc = false;

  Value *Cast = Builder.CreateBitCast(Dest,
                                      Type::getInt8PtrTy(I.getContext()));

  Value *Size = I.getArgOperand(2);
  if (ShouldInc) {
    Value *Cast2 = Builder.CreateBitCast(I.getArgOperand(1)->stripPointerCasts(),
                                         Type::getInt8PtrTy(I.getContext()));
    Builder.CreateCall(IncPtrLog, {Cast2, Size});
    Builder.CreateCall(DecPtrLog, {Cast, Size});
    Builder.CreateCall(CpyPtrLog, {Cast, Cast2, Size});
  } else {
    Builder.CreateCall(DecPtrLog, {Cast, Size});
    Builder.CreateCall(ClearPtrLog, {Cast, Size});
  }
  // handleTy(&I, I.getNextNode(), Dest, ShouldInc);
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts)
    handleScopeExit(Builder, AI, Builder.getInt64(getAllocaSizeInBytes(AI)));
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
  M.getOrInsertFunction("ls_clear_ptrlog",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("ls_copy_ptrlog",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt8PtrTy(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("ls_inc_ptrlog",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("ls_dec_ptrlog",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("malloc_wrap",
                        FunctionType::get(Type::getInt8PtrTy(C),
                                          {Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("calloc_wrap",
                        FunctionType::get(Type::getInt8PtrTy(C),
                                          {Type::getInt64Ty(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("realloc_wrap",
                        FunctionType::get(Type::getInt8PtrTy(C),
                                          {Type::getInt8PtrTy(C),
                                              Type::getInt64Ty(C)}, false));
  M.getOrInsertFunction("free_wrap",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C)}, false));

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
