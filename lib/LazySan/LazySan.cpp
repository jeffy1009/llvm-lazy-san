#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/LazySan/LazySan.h"

#include "LazySanVisitor.h"

#define DEBUG_TYPE "lazy-san"

using namespace llvm;

LazySanVisitor::LazySanVisitor(Module &M, const EQTDDataStructures *dsa,
                               AliasAnalysis *aa)
  : DSA(dsa), AA(aa) {
  DecRC = M.getFunction("ls_dec_refcnt");
  IncRC = M.getFunction("ls_inc_refcnt");
  IncDecRC = M.getFunction("ls_incdec_refcnt");
  ClearPtrLog = M.getFunction("ls_clear_ptrlog");
  CpyPtrLog = M.getFunction("ls_copy_ptrlog");
  CheckPtrLog = M.getFunction("ls_check_ptrlog");
  IncPtrLog = M.getFunction("ls_inc_ptrlog");
  DecPtrLog = M.getFunction("ls_dec_ptrlog");
}

bool LazySanVisitor::checkArrayTy(Type *Ty) {
  Type *ElemTy = Ty->getArrayElementType();
  if (ElemTy->isPointerTy())
    return true;

  if (ElemTy->isArrayTy())
    return checkArrayTy(ElemTy);

  if (ElemTy->isStructTy())
    return checkStructTy(ElemTy);

  // 8 bit integer types are an exception. It is common to cast char buffer
  // to hold different types
  // TODO: see if this is too conservative
  if (ElemTy->isIntegerTy(8))
    return true;

  assert(ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy());
  return false;
}

bool LazySanVisitor::checkStructTy(Type *Ty) {
  for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
    Type *ElemTy = Ty->getStructElementType(i);
    if (ElemTy->isPointerTy())
      return true;

    if (ElemTy->isArrayTy() && checkArrayTy(ElemTy))
      return true;

    if (ElemTy->isStructTy() && checkStructTy(ElemTy))
      return true;

    assert(ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy());
    continue;
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

  // 8 bit integer types are an exception. It is common to cast char buffer
  // to hold different types
  // TODO: see if this is too conservative
  if (ElemTy->isIntegerTy(8))
    return true;

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
  assert(!I.isArrayAllocation());

  // We clear ptrlog regardless of alloca type. We probably could do some
  // optimization to ignore objects without any pointer type member,
  // but for simplicity of design and easy debugging, just clear it all.
  // TODO: merge ptrlog clearing in the backend!
  IRBuilder<> Builder(I.getNextNode());
  handleScopeEntry(Builder, &I, Builder.getInt64(getAllocaSizeInBytes(&I)));

  // But we could ignore those objects when we decrease reference counts
  if (checkTy(I.getType()))
    AllocaInsts.push_back(&I);
}

void LazySanVisitor::visitStoreInst(StoreInst &I) {
  Value *Ptr = I.getValueOperand();
  Type *Ty = Ptr->getType();
  assert(!isa<PtrToIntInst>(Ptr));
  if (!Ty->isPointerTy()) {
    Value *Lhs = I.getPointerOperand();
    // Not using stripPointerCasts here. we don't want to strip all-zero GEP
    if (isa<BitCastInst>(Lhs)) {
      Lhs = cast<BitCastInst>(Lhs)->getOperand(0);
      assert(Lhs == Lhs->stripPointerCasts());
    }
    assert(!isa<PtrToIntInst>(Lhs) && !isa<GlobalAlias>(Lhs));
    PointerType *LhsTy = cast<PointerType>(Lhs->getType());
    if (!checkTy(LhsTy)) {
      assert(!isPointerOperand(Ptr)); // double check with dangsan
      return;
    }
  }

  DSGraph *G = DSA->getDSGraph(*I.getFunction());
  if (DSNode *N = G->getNodeForValue(Ptr).getNode()) {
    assert(!N->isUnknownNode());
    if (N->isCompleteNode() && !N->isHeapNode())
      return;
  }

  // Make sure that we are not missing any optimization that DangSan does

  assert(isPointerOperand(Ptr));
  // Even if RHS is statically known to be null or not a heap pointer, etc,
  // we won't be saving much since we still need to decrease the refcnt of the
  // previously pointed object, unless we also know that we don't have to.
  // TODO: determine if the store is the first store to the location
  /*
  if (isa<FunctionType>(cast<PointerType>(Ty)->getElementType())
      || isStackPointer(Ptr) || isGlobalPointer(Ptr) || isa<ConstantPointerNull>(Ptr));
  */
  if (isSameLoadStore(I.getPointerOperand(), Ptr))
    return;

  IRBuilder<> Builder(&I);

  Value *Cast = Builder.CreateBitOrPointerCast(Ptr,
                                               Type::getInt8PtrTy(I.getContext()));
  Value *Cast2 = Builder.CreateBitOrPointerCast(I.getPointerOperand(),
                                                Type::getInt8PtrTy(I.getContext()));
  Builder.CreateCall(IncDecRC, {Cast, Cast2});
}

void LazySanVisitor::handleLifetimeIntr(IntrinsicInst *I) {
  IRBuilder<> Builder(I);
  AllocaInst *Dest = cast<AllocaInst>(I->getArgOperand(1)->stripPointerCasts());
  assert(!Dest->isArrayAllocation());

  // We clear ptrlog for all types but optimize when we decrease refcnts.
  // (see comments in visitAllocaInst)
  Value *Size = I->getArgOperand(0);
  if (I->getIntrinsicID() == Intrinsic::lifetime_start)
    handleScopeEntry(Builder, Dest, Size);
  else if (checkTy(Dest->getType()))
    handleScopeExit(Builder, Dest, Size);
}

void LazySanVisitor::handleMemSet(CallInst *I) {
  IRBuilder<> Builder(I);
  Value *Dest = I->getArgOperand(0)->stripPointerCasts();
  Value *DestCast =
    Builder.CreateBitCast(Dest, Type::getInt8PtrTy(I->getContext()));
  Value *Size = I->getArgOperand(2);
  if (!checkTy(Dest->getType())) {
    Builder.CreateCall(CheckPtrLog, {DestCast, Size});
    return;
  }

  Builder.CreateCall(DecPtrLog, {DestCast, Size});
  Builder.CreateCall(ClearPtrLog, {DestCast, Size});
}

void LazySanVisitor::handleMemTransfer(CallInst *I) {
  IRBuilder<> Builder(I);
  Value *Dest = I->getArgOperand(0)->stripPointerCasts();
  Value *DestCast =
    Builder.CreateBitCast(Dest, Type::getInt8PtrTy(I->getContext()));
  Value *Src = I->getArgOperand(1)->stripPointerCasts();
  Value *SrcCast =
    Builder.CreateBitCast(Src, Type::getInt8PtrTy(I->getContext()));
  Value *Size = I->getArgOperand(2);
  if (!checkTy(Dest->getType()) && !checkTy(Src->getType())) {
    Builder.CreateCall(CheckPtrLog, {DestCast, Size});
    Builder.CreateCall(CheckPtrLog, {SrcCast, Size});
    return;
  }

  Builder.CreateCall(IncPtrLog, {SrcCast, Size});
  Builder.CreateCall(DecPtrLog, {DestCast, Size});
  Builder.CreateCall(CpyPtrLog, {DestCast, SrcCast, Size});
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

  if (isa<MemSetInst>(&I)
      || CalledFunc->getName().equals("memset"))
    return handleMemSet(&I);

  if (isa<MemTransferInst>(&I)
      || CalledFunc->getName().equals("memmove")
      || CalledFunc->getName().equals("memcpy"))
    return handleMemTransfer(&I);
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts)
    handleScopeExit(Builder, AI, Builder.getInt64(getAllocaSizeInBytes(AI)));
}

char LazySan::ID = 0;

static RegisterPass<LazySan> X("lazy-san", "Lazy Pointer Sanitizer Pass");

LazySan::LazySan() : ModulePass(ID) {
  initializeAAResultsWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool LazySan::runOnFunction(Function &F) {
  LazySanVisitor LSV(*F.getParent(), &getAnalysis<EQTDDataStructures>(),
                     &getAnalysis<AAResultsWrapperPass>(F).getAAResults());

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
  M.getOrInsertFunction("ls_incdec_refcnt",
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
  M.getOrInsertFunction("ls_check_ptrlog",
                        FunctionType::get(Type::getVoidTy(C),
                                          {Type::getInt8PtrTy(C),
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
  AU.addRequired<EQTDDataStructures>();
  AU.addRequired<AAResultsWrapperPass>();
  AU.setPreservesCFG();
}
