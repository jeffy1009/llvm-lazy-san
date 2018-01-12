#include "LazySanVisitor.h"

using namespace llvm;

#define DEBUG_MSG(err)

bool LazySanVisitor::isSameLoadStore(Value *ptr_addr, Value *obj_addr) {
  if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(obj_addr)) {
    if (LoadInst *LI = dyn_cast<LoadInst>(GEP->getPointerOperand())) {
      if (ptr_addr == LI->getPointerOperand()) {
        return true;
      }
    }
  }
  return false;
}

bool LazySanVisitor::isStackPointer(Value *V) {
  if (isa<AllocaInst>(V)) {
    DEBUG_MSG(errs() << "Stack variable \n");
    return true;
  }

  if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
    return isStackPointer(BC->getOperand(0));
  } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
    return isStackPointer(PI->getOperand(0));
  } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
    return isStackPointer(GEP->getPointerOperand());
  }

  DEBUG_MSG(errs() << "Not a Stack variable \n");
  return false;
}

bool LazySanVisitor::isGlobalPointer(Value *V) {
  V = V->stripPointerCasts();
  if (isa<GlobalValue>(V) || AA->pointsToConstantMemory(V)) {
    return true;
  }

  if (BitCastInst *BC = dyn_cast<BitCastInst>(V)) {
    return isGlobalPointer(BC->getOperand(0));
  } else if (PtrToIntInst *PI = dyn_cast<PtrToIntInst>(V)) {
    return isGlobalPointer(PI->getOperand(0));
  } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
    return isGlobalPointer(GEP->getPointerOperand());
  } else if (LoadInst *LI = dyn_cast<LoadInst>(V)) {          /* TODO: Remove load instruction */
    if (AA->pointsToConstantMemory(LI->getOperand(0))) {
      DEBUG_MSG(errs() << "Global constant load \n");
      return true;
    }
  } else if (SelectInst *SI = dyn_cast<SelectInst>(V)) {
    return (isGlobalPointer(SI->getTrueValue()) && isGlobalPointer(SI->getFalseValue()));
  }
  return false;
}

bool LazySanVisitor::isPointerOperand(Value *V) {
  if (V->getType()->isPointerTy()) {
    DEBUG_MSG(errs() << "Direct Pointer Type \n");
    return true;
  }
  if (isa<PtrToIntInst>(V)) {
    DEBUG_MSG(errs() << "Pointer to int type cast \n");
    return true;
  }

  /*
   * Load instruction with Pointer operand beign
   * Bitcast or GEP.
   */
  if (LoadInst *LI = dyn_cast<LoadInst>(V)) {
    DEBUG_MSG(errs () << "Load Instruction \n");
    Value *LoadPtr = LI->getPointerOperand();
    if (isDoublePointer(LoadPtr)) {
      DEBUG_MSG(errs() << "Load double pointer type \n");
      return true;
    }
    Value *DeepLoadPtr = nullptr;
    Instruction *Inst = nullptr;
    /* Handle Constant Expression */
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(LoadPtr)) {
      /*
       * Note: Be careful with constant expression. getAsInstruction() creates
       * Dangling reference. TODO: remove this and operate only on CE
       */
      Inst = CE->getAsInstruction();
    } else {
      Inst = dyn_cast<Instruction>(LoadPtr);
    }

    if (const BitCastInst *BC = dyn_cast_or_null<BitCastInst>(Inst)) {
      DEBUG_MSG(errs() << "Bit cast deep instruction \n");
      DeepLoadPtr = BC->getOperand(0);
    } else if (GetElementPtrInst *GEPI = dyn_cast_or_null<GetElementPtrInst>(Inst)) {
      DEBUG_MSG(errs() << "Get Element constant expression \n");
      DeepLoadPtr = GEPI->getPointerOperand();
    }

    if (isa<ConstantExpr>(LoadPtr)) {
      Inst->dropAllReferences();
    }

    if (DeepLoadPtr && isDoublePointer(DeepLoadPtr)) {
      DEBUG_MSG(errs() << "Double pointer type \n");
      return true;
    }
  }
  return false;
}

bool LazySanVisitor::isDoublePointer(Value *V) {
  const Type* T = V->getType();
  return T->isPointerTy() && T->getContainedType(0)->isPointerTy();
}
