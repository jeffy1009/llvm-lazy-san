#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/VectorUtils.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/LazySan/LazySan.h"

#include "LazySanVisitor.h"

#define DEBUG_TYPE "lazy-san"

using namespace llvm;

cl::opt<bool>
EnableChecks("lazysan-enable-check",
             cl::desc("Enable lazy-san sanity checking"),
             cl::init(false));

cl::opt<bool>
EnableDSA("lazysan-enable-dsa",
             cl::desc("Enable DSA in lazy-san which can slow down build time"),
             cl::init(false));

LazySanVisitor::LazySanVisitor(Module &M, const EQTDDataStructures *dsa,
                               AliasAnalysis *aa)
  : DSA(dsa), AA(aa) {
  DecRC = M.getFunction("ls_dec_refcnt");
  IncRC = M.getFunction("ls_inc_refcnt");
  IncDecRC = M.getFunction("ls_incdec_refcnt");
  IncDecRC_noinc = M.getFunction("ls_incdec_refcnt_noinc");
  ClearPtrLog = M.getFunction("ls_clear_ptrlog");
  CpyPtrLog = M.getFunction("ls_copy_ptrlog");
  CheckPtrLog = M.getFunction("ls_check_ptrlog");
  IncPtrLog = M.getFunction("ls_inc_ptrlog");
  DecPtrLog = M.getFunction("ls_dec_ptrlog");
  DecAndClearPtrLog = M.getFunction("ls_dec_clear_ptrlog");
  IncDecCpyPtrLog = M.getFunction("ls_incdec_copy_ptrlog");
  IncDecMovePtrLog = M.getFunction("ls_incdec_move_ptrlog");
}

bool LazySanVisitor::checkArrayTy(Type *Ty, bool IgnoreI8) {
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
  if (!IgnoreI8 && ElemTy->isIntegerTy(8))
    return true;

  assert(ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy());
  return false;
}

// TODO: check if we are handling unions correctly
bool LazySanVisitor::checkStructTy(Type *Ty) {
  for (unsigned int i = 0, e = Ty->getStructNumElements(); i < e; ++i) {
    Type *ElemTy = Ty->getStructElementType(i);
    if (ElemTy->isPointerTy())
      return true;

    if (ElemTy->isArrayTy()) {
      if (checkArrayTy(ElemTy))
        return true;
    } else if (ElemTy->isStructTy()) {
      if (checkStructTy(ElemTy))
        return true;
    } else {
      assert(ElemTy->isIntegerTy() || ElemTy->isFloatingPointTy());
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
                                     Value *Size, bool Check) {
  Value *Cast = B.CreateBitCast(Dest, Type::getInt8PtrTy(Dest->getContext()));
  // handleTy(&I, nullptr, Dest, false);
  B.CreateCall(Check? CheckPtrLog : DecPtrLog, {Cast, Size});
}

// Code copied from lib/Transforms/Instrumentation/AddressSanitizer.cpp
static uint64_t getAllocaSizeInBytes(AllocaInst *AI) {
  Type *Ty = AI->getAllocatedType();
  uint64_t SizeInBytes =
    AI->getModule()->getDataLayout().getTypeAllocSize(Ty);
  return SizeInBytes;
}

static void setNearestDebugLocation(IRBuilder<> &B, Instruction *InstDL) {
  while (!InstDL->getDebugLoc()) InstDL = InstDL->getNextNode();
  B.SetCurrentDebugLocation(InstDL->getDebugLoc());
}

void LazySanVisitor::visitAllocaInst(AllocaInst &I) {
  // Allocas having lifetime markders will be processed at the lifetime markers
  if (hasLifetimeMarkers(&I))
    return;

  // TODO: handle allocas not in the entry block (in gcc)
  if (I.getParent() != &I.getFunction()->getEntryBlock())
    return;
  // assert(I.getParent() == &I.getFunction()->getEntryBlock()
  //        && "alloca not in the entry basic block!");
  // assert(I.isStaticAlloca());
  // assert(!I.isArrayAllocation());
  BasicBlock *BB = I.getParent();
  Instruction *InsertPos = I.getNextNode();
  while (isa<AllocaInst>(InsertPos) || isa<DbgInfoIntrinsic>(InsertPos))
    InsertPos = InsertPos->getNextNode();
  assert(InsertPos->getParent()==BB);

  IRBuilder<> Builder(InsertPos);

  // Allocas may not have !dbg metadata. Find nearest one. LLVM will sometimes
  // complain if we don't do this.
  setNearestDebugLocation(Builder, &I);

  // We clear ptrlog regardless of alloca type. We probably could do some
  // optimization to ignore objects without any pointer type member,
  // but for simplicity of design and easy debugging, just clear it all.
  // TODO: merge ptrlog clearing in the backend!
  handleScopeEntry(Builder, &I, Builder.getInt64(getAllocaSizeInBytes(&I)));

  // But we could ignore those objects when we decrease reference counts
  if (checkTy(I.getType()))
    AllocaInsts.push_back(&I);
  else if (EnableChecks)
    AllocaInstsCheck.push_back(&I);
}

static bool isUnionTy(Type *Ty) {
  return isa<StructType>(Ty)
    && !cast<StructType>(Ty)->isLiteral()
    && cast<StructType>(Ty)->getName().startswith("union");
}

// TODO: do similar thing with RHS
bool LazySanVisitor::shouldInstrument(Value *V,
                                      SmallPtrSetImpl<Value *> &Visited,
                                      bool LookForUnion) {
  // Avoid recursion due to PHIs in Loops
  if (!Visited.insert(V).second)
    return false;

  if (!isa<User>(V))
    assert(isa<Argument>(V));
  if (isa<Constant>(V))
    assert(isa<ConstantExpr>(V) || isa<ConstantPointerNull>(V)
           || isa<GlobalVariable>(V) || isa<UndefValue>(V));
  if (isa<ConstantExpr>(V))
    assert(cast<ConstantExpr>(V)->getOpcode() == Instruction::BitCast
           || cast<ConstantExpr>(V)->getOpcode() == Instruction::GetElementPtr
           || cast<ConstantExpr>(V)->getOpcode() == Instruction::IntToPtr);
  if (isa<Instruction>(V))
    assert(isa<AllocaInst>(V) || isa<BitCastInst>(V) || isa<CallInst>(V)
           || isa<ExtractValueInst>(V) || isa<GetElementPtrInst>(V)
           || isa<IntToPtrInst>(V) || isa<InvokeInst>(V) || isa<LoadInst>(V)
           || isa<PHINode>(V) || isa<SelectInst>(V));

  // TODO: Handling bitcasts and getelementptrs are not 100% accurate.
  if (isa<BitCastInst>(V)
      || (isa<ConstantExpr>(V)
          && cast<ConstantExpr>(V)->getOpcode() == Instruction::BitCast)) {
    Value *BCI = cast<User>(V)->getOperand(0);
    // BCI should be a pointer type
    Type *ElemTy = BCI->getType()->getPointerElementType();
    assert(!(ElemTy->isVectorTy() && !ElemTy->getScalarType()->isIntegerTy()));
    // TODO: there's an exceptional case where the following assertion fails in perlbench
    // in S_unpack_rec function due to SROA.
    // assert(LookForUnion
    //        || !(ElemTy->isStructTy() &&
    //             !(isUnionTy(ElemTy) && ElemTy->getStructNumElements()==1)));
    assert(!(ElemTy->isArrayTy() && checkArrayTy(ElemTy, true)));
    if (!LookForUnion
        && (isDoublePointer(BCI)
            || (ElemTy->isStructTy() && ElemTy->getStructNumElements()==1
                && ElemTy->getStructElementType(0)->isPointerTy())
            || (ElemTy->isArrayTy() && ElemTy->getArrayElementType()->isIntegerTy(8))))
      return true;
    return shouldInstrument(BCI, Visited, LookForUnion);
  }

  if (isa<GetElementPtrInst>(V)
      || (isa<ConstantExpr>(V)
           && cast<ConstantExpr>(V)->getOpcode() == Instruction::GetElementPtr)) {
    // TODO: currently if we meet any union types with any pointer field in it,
    // we decide to instrument it
    // TODO: checkStructTy will only visit one of the union member. fix it.
    User *GEP = cast<User>(V);
    for (gep_type_iterator GTI = gep_type_begin(GEP), GTE = gep_type_end(GEP);
         GTI != GTE; ++GTI)
      if (isUnionTy(*GTI) && checkStructTy(*GTI))
        return true;
    return shouldInstrument(GEP->getOperand(0), Visited,
                            GEP->getNumOperands() > 2 ? true : false);
  }

  if (PHINode *Phi = dyn_cast<PHINode>(V)) {
    bool Should = false;
    for (unsigned i = 0, e = Phi->getNumIncomingValues(); i != e; i++)
      Should |= shouldInstrument(Phi->getIncomingValue(i), Visited,
                                 LookForUnion);
    return Should;
  }

  if (SelectInst *SI = dyn_cast<SelectInst>(V))
    return shouldInstrument(SI->getTrueValue(), Visited, LookForUnion)
      || shouldInstrument(SI->getFalseValue(), Visited, LookForUnion);

  // TODO: should we handle LoadInst?
  return false;
}

static bool visitConstant(Constant *C) {
  if (isa<GlobalVariable>(C))
    return false;

  switch (cast<ConstantExpr>(C)->getOpcode()) {
  case Instruction::BitCast:
    return visitConstant(cast<Constant>(C->stripPointerCasts()));
  case Instruction::GetElementPtr:
    return visitConstant(cast<Constant>(C->getOperand(0)));
  case Instruction::IntToPtr: // very rare case..
    return false;
  default:
    assert(0);
  }
}

bool LazySanVisitor::maybeHeapPtr(Value *V, SmallPtrSetImpl<Value *> &Visited) {
  if (!Visited.insert(V).second)
    return false;

  Type *Ty = V->getType();
  if (Ty->isPointerTy() && Ty->getPointerElementType()->isFunctionTy())
    return false;

  if (isa<Argument>(V))
    return true;

  if (isa<ConstantPointerNull>(V) || isa<GlobalValue>(V)
      || AA->pointsToConstantMemory(V))
    return false;

  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V))
    return visitConstant(CE);

  switch (cast<Instruction>(V)->getOpcode()) {
  case Instruction::Alloca:
    return false;
  case Instruction::Call:
  case Instruction::IntToPtr:
  case Instruction::PtrToInt:
    return true;
  case Instruction::Load: {
    if (AA->pointsToConstantMemory(cast<LoadInst>(V)->getOperand(0)))
      return false;
    return true;
  }
  case Instruction::BitCast:
    return maybeHeapPtr(cast<BitCastInst>(V)->stripPointerCasts(), Visited);
  case Instruction::GetElementPtr:
    return maybeHeapPtr(cast<GetElementPtrInst>(V)->getPointerOperand(), Visited);
  case Instruction::PHI: {
    PHINode *Phi = cast<PHINode>(V);
    bool Maybe = false;
    for (unsigned i = 0, e = Phi->getNumIncomingValues(); i != e; i++)
      Maybe |= maybeHeapPtr(Phi->getIncomingValue(i), Visited);
    return Maybe;
  }
  case Instruction::Select: {
    SelectInst *SI = cast<SelectInst>(V);
    return maybeHeapPtr(SI->getTrueValue(), Visited)
      || maybeHeapPtr(SI->getFalseValue(), Visited);
  }
  default:
    assert(0);
  }
}

// TODO: complete vectorization support
void LazySanVisitor::visitStoreInst(StoreInst &I) {
  Value *Ptr = I.getValueOperand();
  Value *Lhs = I.getPointerOperand();
  Type *Ty = Ptr->getType();
  Type *ScalarTy = Ty->getScalarType();
  assert(!Ty->isVectorTy() && "vectorization support not yet complete!");
  bool NeedInc = true;
  // TODO: make sure that we are not skipping any instructions we need to handle
  // and skipping those we don't
  if (!ScalarTy->isPointerTy() && !isa<PtrToIntInst>(Ptr)) {
    // Ptr is probably not a pointer. Don't need to increase refcnt
    NeedInc = false;
    // Here we search for possible union type store.
    // We need this because pointer may be overwritten by non-pointer
    // (and we have to decrease refcnt in that case)
    SmallPtrSet<Value *, 8> Visited;
    if (!shouldInstrument(Lhs, Visited)) {
      //assert(!isPointerOperand(Ptr));   // double check with dangsan
      return;
    }
    //assert(!isPointerOperand(Ptr));
  }

  if (EnableDSA) {
    DSGraph *G = DSA->getDSGraph(*I.getFunction());
    if (DSNode *N = G->getNodeForValue(Ptr).getNode()) {
      assert(!N->isUnknownNode());
      if (N->isCompleteNode() && !N->isHeapNode())
        return;
    }
  }

  if (isSameLoadStore(Lhs, Ptr))
    return;

  // TODO: determine if the store is the first store to the location
  SmallPtrSet<Value *, 8> Visited;
  if (NeedInc && !maybeHeapPtr(Ptr, Visited))
    NeedInc = false;

  IRBuilder<> Builder(&I);
  setNearestDebugLocation(Builder, &I);

  Value *DstCast =
    Builder.CreateBitOrPointerCast(Lhs, Type::getInt8PtrTy(I.getContext()));
  Value *SrcCast;
  if (NeedInc) {
    SrcCast =
      Builder.CreateBitOrPointerCast(Ptr, Type::getInt8PtrTy(I.getContext()));
    Builder.CreateCall(IncDecRC, {SrcCast, DstCast});
  } else {
    Builder.CreateCall(IncDecRC_noinc, {DstCast});
  }
}

void LazySanVisitor::handleLifetimeIntr(IntrinsicInst *I) {
  IRBuilder<> Builder(I);
  Value *Arg = I->getArgOperand(1);
  // encountered PHI node in gcc..
  if (PHINode *Phi = dyn_cast<PHINode>(Arg))
    Arg = Phi->getIncomingValue(0);
  AllocaInst *Dest = cast<AllocaInst>(Arg->stripPointerCasts());
  assert(!Dest->isArrayAllocation());

  // We clear ptrlog for all types but optimize when we decrease refcnts.
  // (see comments in visitAllocaInst)
  Value *Size = I->getArgOperand(0);
  if (I->getIntrinsicID() == Intrinsic::lifetime_start)
    handleScopeEntry(Builder, Dest, Size);
  else if (checkTy(Dest->getType()))
    handleScopeExit(Builder, Dest, Size);
  else if (EnableChecks)
    handleScopeExit(Builder, Dest, Size, /* Check = */ true);
}

void LazySanVisitor::handleMemSet(CallInst *I) {
  IRBuilder<> Builder(I);
  Value *Dest = I->getArgOperand(0)->stripPointerCasts();
  Value *DestCast =
    Builder.CreateBitCast(Dest, Type::getInt8PtrTy(I->getContext()));
  Value *Size = I->getArgOperand(2);
  if (!checkTy(Dest->getType())) {
    if (EnableChecks)
      Builder.CreateCall(CheckPtrLog, {DestCast, Size});
    return;
  }

  Builder.CreateCall(DecAndClearPtrLog, {DestCast, Size});
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
    if (EnableChecks) {
      Builder.CreateCall(CheckPtrLog, {DestCast, Size});
      Builder.CreateCall(CheckPtrLog, {SrcCast, Size});
    }
    return;
  }

  if (isa<MemCpyInst>(I)
      || I->getCalledFunction()->getName().equals("memcpy"))
    Builder.CreateCall(IncDecCpyPtrLog, {DestCast, SrcCast, Size});
  else
    Builder.CreateCall(IncDecMovePtrLog, {DestCast, SrcCast, Size});
}

void LazySanVisitor::visitCallSite(CallSite CS) {
  Instruction &I = *CS.getInstruction();
  Function *CalledFunc = CS.getCalledFunction();
  if (!CalledFunc) // skip indirect calls
    return;

  if (IntrinsicInst *Intr = dyn_cast<IntrinsicInst>(&I))
    if (Intr->getIntrinsicID() == Intrinsic::lifetime_start
        || Intr->getIntrinsicID() == Intrinsic::lifetime_end)
      return handleLifetimeIntr(Intr);

  IRBuilder<> Builder(&I);

  if (isa<MemSetInst>(&I)
      || CalledFunc->getName().equals("memset"))
    return handleMemSet(cast<CallInst>(&I));

  if (isa<MemTransferInst>(&I)
      || CalledFunc->getName().equals("memmove")
      || CalledFunc->getName().equals("memcpy"))
    return handleMemTransfer(cast<CallInst>(&I));
}

void LazySanVisitor::visitReturnInst(ReturnInst &I) {
  IRBuilder<> Builder(&I);

  for (AllocaInst *AI : AllocaInsts)
    handleScopeExit(Builder, AI, Builder.getInt64(getAllocaSizeInBytes(AI)));

  for (AllocaInst *AI : AllocaInstsCheck)
    handleScopeExit(Builder, AI, Builder.getInt64(getAllocaSizeInBytes(AI)),
                    /* Check = */ true);
}

char LazySan::ID = 0;

static RegisterPass<LazySan> X("lazy-san", "Lazy Pointer Sanitizer Pass");

LazySan::LazySan() : ModulePass(ID) {
  initializeAAResultsWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool LazySan::runOnFunction(Function &F) {
  LazySanVisitor LSV(*F.getParent(),
                     EnableDSA ? &getAnalysis<EQTDDataStructures>() : nullptr,
                     &getAnalysis<AAResultsWrapperPass>(F).getAAResults());

  LSV.visit(F);

  // To force linking
  if (F.getName().startswith("abcdef")) {
    F.viewCFGOnly();
    F.viewCFG();
  }

  return true;
}

// IMPORTANT: make sure these include all functions in the static lib
static char const *LSFuncs[] = {
  "atexit_hook", "init_lazysan", "sys_mmap", "get_obj_info", "delete_obj_info", "ls_free", "alloc_common", "alloc_obj_info", "free_common", "ls_dec_refcnt", "ls_inc_refcnt", "ls_incdec_refcnt_noinc", "ls_incdec_refcnt", "ls_clear_ptrlog", "ls_copy_ptrlog", "ls_incdec_copy_ptrlog", "ls_incdec_move_ptrlog", "ls_check_ptrlog", "ls_inc_ptrlog", "ls_dec_ptrlog", "ls_dec_clear_ptrlog", "malloc_wrap", "calloc_wrap", "realloc_wrap", "free_wrap", "_Znwm_wrap", "_Znam_wrap", "_ZdlPv_wrap", "_ZdaPv_wrap",
  "metaset_4", "metaset_8", "metaget_4", "metaget_8",
  "RBTreeCompare", "RBTreeCreate", "LeftRotate", "RightRotate", "TreeInsertHelp", "RBTreeInsert", "TreeSuccessor", "InorderTreePrint", "TreeDestHelper", "RBTreeDestroy", "RBTreePrint", "RBExactQuery", "RBDeleteFixUp", "RBDelete"
};

static bool isLSFunc(StringRef name) {
  bool Found = false;
  for (unsigned int i = 0; i < (sizeof(LSFuncs) / sizeof(LSFuncs[0])); ++i)
    Found |= StringRef(LSFuncs[i]).equals(name);
  return Found;
}

bool LazySan::runOnModule(Module &M) {
  dbgs() << "Hello World!!!\n";
  for (Function &F : M.functions()) {
    if (F.empty() || isLSFunc(F.getName()))
      continue;

    runOnFunction(F);
  }

  static char const *MMFuncs[] = {
    "malloc", "calloc", "realloc", "free", "_Znwm", "_Znam", "_ZdlPv", "_ZdaPv"
  };

  // to handle indirect calls to malloc/frees
  for (unsigned int i = 0; i < (sizeof(MMFuncs) / sizeof(MMFuncs[0])); ++i) {
    SmallString<16> WrapName;
    Function *Orig = M.getFunction(MMFuncs[i]);
    if (!Orig) continue;
    Function *Wrap = M.getFunction((Twine(MMFuncs[i])+"_wrap").toStringRef(WrapName));
    // Need to gather users first instead of changing directly, to not mess
    // with the iterator...
    SmallVector<Use *, 4> Uses;
    for (Use &U : Orig->uses()) {
      User *Usr = U.getUser();
      if (Instruction *Inst = dyn_cast<Instruction>(Usr)) {
        if (isLSFunc(Inst->getFunction()->getName()))
          continue;
      } else {
        Constant *C = cast<Constant>(Usr);
        for (User *CU : C->users())
          assert(!isLSFunc(cast<Instruction>(CU)->getFunction()->getName()));
      }
      Uses.push_back(&U);
    }

    for (Use *U : Uses) {
      User *Usr = U->getUser();
      if (isa<Instruction>(Usr))
        Usr->replaceUsesOfWith(Orig, Wrap);
      else
        cast<Constant>(Usr)->handleOperandChange(Orig, Wrap, U);
    }
  }

  return true;
}

void LazySan::getAnalysisUsage(AnalysisUsage &AU) const {
  if (EnableDSA)
    AU.addRequired<EQTDDataStructures>();
  AU.addRequired<AAResultsWrapperPass>();
  AU.setPreservesCFG();
}
