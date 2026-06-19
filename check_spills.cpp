#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Coroutines/SuspendCrossingInfo.h"

using namespace llvm;

static void splitBlockIfNotFirst(Instruction *I, const Twine &Name) {
  BasicBlock *BB = I->getParent();
  if (&BB->front() == I)
    return;
  BB->splitBasicBlock(I, Name);
}
static void splitAround(Instruction *I, const Twine &Name) {
  splitBlockIfNotFirst(I, Name);
  splitBlockIfNotFirst(I->getNextNode(), "After" + Name);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    errs() << "Usage: " << argv[0] << " <ir_file.ll>\n";
    return 1;
  }

  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseIRFile(argv[1], Err, Context);
  if (!M) {
    Err.print(argv[0], errs());
    return 1;
  }

  for (Function &F : *M) {
    if (F.isDeclaration()) continue;

    SmallVector<AnyCoroSuspendInst *, 4> CoroSuspends;
    SmallVector<AnyCoroEndInst *, 4> CoroEnds;

    for (Instruction &I : instructions(F)) {
      if (auto *S = dyn_cast<AnyCoroSuspendInst>(&I)) {
        CoroSuspends.push_back(S);
      } else if (auto *E = dyn_cast<AnyCoroEndInst>(&I)) {
        CoroEnds.push_back(E);
      }
    }

    if (CoroSuspends.empty()) continue;

    for (AnyCoroSuspendInst *CSI : CoroSuspends) {
      splitAround(CSI, "CoroSuspend");
    }
    for (AnyCoroEndInst *CE : CoroEnds) {
      splitAround(CE, "CoroEnd");
    }

    outs() << "=== Analyzing Coroutine Function: " << F.getName() << " (" << CoroSuspends.size() << " suspends) ===\n";

    SuspendCrossingInfo Checker(F, CoroSuspends, CoroEnds);

    for (Argument &Arg : F.args()) {
      for (User *U : Arg.users()) {
        if (Checker.isDefinitionAcrossSuspend(Arg, U)) {
          outs() << "  [SPILL ARG Def]: Argument #" << Arg.getArgNo() << ": " << Arg << "\n";
          outs() << "    Def Location: Function Parameter #" << Arg.getArgNo() << " of " << F.getName() << "\n";
          if (auto *UI = dyn_cast<Instruction>(U)) {
            outs() << "    -> [User in Basic Block ";
            if (UI->getParent())
              UI->getParent()->printAsOperand(outs(), false);
            else
              outs() << "<no bb>";
            for (unsigned OpIdx = 0; OpIdx < UI->getNumOperands(); ++OpIdx) {
              if (UI->getOperand(OpIdx) == &Arg)
                outs() << ", Operand #" << OpIdx;
            }
            outs() << "]: " << *UI << "\n";
            outs() << "       Use Location: ";
            if (const DebugLoc &DL = UI->getDebugLoc())
              DL.print(outs());
            else
              outs() << "<no debug loc>";
            outs() << "\n";
          } else {
            outs() << "    -> [User]: " << *U << "\n";
          }
        }
      }
    }

    for (Instruction &I : instructions(F)) {
      if (isa<AnyCoroIdInst>(&I) || isa<CoroBeginInst>(&I) || isa<CoroFreeInst>(&I))
        continue;

      for (User *U : I.users()) {
        if (Checker.isDefinitionAcrossSuspend(I, U)) {
          outs() << "  [SPILL INST Def]: Instruction in Basic Block ";
          if (I.getParent())
            I.getParent()->printAsOperand(outs(), false);
          else
            outs() << "<no bb>";
          outs() << ": " << I << "\n";
          outs() << "    Def Location: ";
          if (const DebugLoc &DL = I.getDebugLoc())
            DL.print(outs());
          else
            outs() << "<no debug loc>";
          outs() << "\n";

          if (auto *UI = dyn_cast<Instruction>(U)) {
            outs() << "    -> [User in Basic Block ";
            if (UI->getParent())
              UI->getParent()->printAsOperand(outs(), false);
            else
              outs() << "<no bb>";
            for (unsigned OpIdx = 0; OpIdx < UI->getNumOperands(); ++OpIdx) {
              if (UI->getOperand(OpIdx) == &I)
                outs() << ", Operand #" << OpIdx;
            }
            outs() << "]: " << *UI << "\n";
            outs() << "       Use Location: ";
            if (const DebugLoc &DL = UI->getDebugLoc())
              DL.print(outs());
            else
              outs() << "<no debug loc>";
            outs() << "\n";
          } else {
            outs() << "    -> [User]: " << *U << "\n";
          }
        }
      }
    }
  }

  return 0;
}
