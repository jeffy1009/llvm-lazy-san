#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"

#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"

namespace llvm {

class LazySanVisitor : public InstVisitor<LazySanVisitor> {
  const EQTDDataStructures *DSA;
  AliasAnalysis *AA;

  // allocas to be processed at return
  SmallVector<AllocaInst *, 16> AllocaInsts;

  Function *DecRC, *IncRC;
  Function *ClearPtrLog, *CpyPtrLog, *IncPtrLog, *DecPtrLog;

 public:
 LazySanVisitor(Module &M, const EQTDDataStructures *dsa, AliasAnalysis *aa)
   : DSA(dsa), AA(aa) {
    DecRC = M.getFunction("ls_dec_refcnt");
    IncRC = M.getFunction("ls_inc_refcnt");
    ClearPtrLog = M.getFunction("ls_clear_ptrlog");
    CpyPtrLog = M.getFunction("ls_copy_ptrlog");
    IncPtrLog = M.getFunction("ls_inc_ptrlog");
    DecPtrLog = M.getFunction("ls_dec_ptrlog");
  }

  void visitAllocaInst(AllocaInst &I);
  void visitStoreInst(StoreInst &I);

  void visitCallInst(CallInst &I);
  void visitReturnInst(ReturnInst &I);

 private:
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

  void handleLifetimeIntr(IntrinsicInst *I);

  // Code from DangSan
  bool isSameLoadStore(Value *ptr_addr, Value *obj_addr);
  bool isStackPointer(Value *V);
  bool isGlobalPointer(Value *V);
  bool isPointerOperand(Value *V);
  bool isDoublePointer(Value *V);
};

}
