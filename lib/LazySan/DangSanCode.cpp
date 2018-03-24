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
    if (isDoublePointer(LoadPtr->getType())) {
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

    if (DeepLoadPtr && isDoublePointer(DeepLoadPtr->getType())) {
      DEBUG_MSG(errs() << "Double pointer type \n");
      return true;
    }
  }
  return false;
}

bool LazySanVisitor::isDoublePointer(Type *T) {
  return T->isPointerTy() && T->getContainedType(0)->isPointerTy();
}
