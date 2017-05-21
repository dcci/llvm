//===- Backpropagation.cpp - USE to DEF information backpropagation -------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements backpropagation of informations from uses to defs.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/TinyPtrVector.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/DebugCounter.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

#define DEBUG_TYPE "backprop"

namespace {

class PropagatedInfo {
public:
  bool IgnoreSign;

  PropagatedInfo(bool Optimistic = false) : IgnoreSign(Optimistic) {}

  bool canUseInfo() { return IgnoreSign; }
};

class BackPropagationImpl {
  Function &F;
  SmallPtrSet<BasicBlock *, 8> VisitedBlocks;
  DenseSet<Instruction *> CandidateSet;

  void process(BasicBlock *);
  void processInstruction(Instruction &);
  void processUse(Use &, PropagatedInfo &);

public:
  BackPropagationImpl(Function &F) : F(F){};
  bool runBackProp();
};
} // end anonymous namespace

void BackPropagationImpl::processUse(Use &U, PropagatedInfo &PI) {
  auto *I = cast<Instruction>(U.get());
  DEBUG(dbgs() << "Processing use: " << U << " in " << *I << "\n");
  auto *II = dyn_cast<IntrinsicInst>(I);
  if (II) {
    switch (II->getIntrinsicID()) {
    default:
      break;
    case Intrinsic::cos:
      /* sign doesn't matter */
      PI.IgnoreSign = true;
      break;
    }
  }
}

void BackPropagationImpl::processInstruction(Instruction &I) {
  PropagatedInfo PI(true /* Optimistic */);

  // Don't bother looking at instructions with no uses as they
  // can't be helpful for our pass.
  if (I.use_empty())
    return;

  bool Interesting = true;
  for (Use &U : I.uses()) {
    auto *UI = dyn_cast<Instruction>(U.get());
    if (!UI)
      continue;

    // Skip PHI nodes in unprocessed blocks.
    if (isa<PHINode>(UI) && !VisitedBlocks.count(I.getParent())) {
      DEBUG(dbgs() << "Skipping unprocessed PHI: " << *UI << "\n");
      continue;
    }

    // Finally process the use.
    PropagatedInfo UPI;
    processUse(U, UPI);

    // If we find an use that makes our information non propagatable
    // anymore, we give up.
    if (!PI.canUseInfo()) {
      Interesting = false;
      break;
    }
  }

  if (!Interesting)
    return;

  if (CandidateSet.insert(&I).second) {
    // This is the first time we see this DEF.
    // XXX: insert in the interesting postorder set.
  }
  // OK, we found a good candidate for propagation.
}

void BackPropagationImpl::process(BasicBlock *BB) {
  for (auto &I : reverse(*BB)) {
    if (isa<PHINode>(I)) {
      processInstruction(I);
      return;
    }
    processInstruction(I);
  }
}

bool BackPropagationImpl::runBackProp() {
  PostOrderTraversal<Function *> POT(&F);

  // Debug.
  for (auto &BB : POT) {
    DEBUG(dbgs() << "Dumping BB: "
                 << "\n");
    DEBUG(dbgs() << BB << "\n");
  }

  for (auto &BB : POT) {
    process(BB);

    // Mark this block as processed.
    VisitedBlocks.insert(BB);
  }

  return false;
}

class BackPropagationPass : public FunctionPass {
public:
  void getAnalysisUsage(AnalysisUsage &AU) const override {}

  static char ID; // Pass identification, replacement for typeid

  BackPropagationPass() : FunctionPass(ID) {
    initializeBackPropagationPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override {
    if (skipFunction(F))
      return false;
    return BackPropagationImpl(F).runBackProp();
  }
};

char BackPropagationPass::ID = 0;
INITIALIZE_PASS_BEGIN(BackPropagationPass, "backprop",
                      "Backpropagation of informations", false, false)
INITIALIZE_PASS_END(BackPropagationPass, "backprop",
                    "BackPropagation of informations", false, false)

// chis is the public interface to this file.
FunctionPass *llvm::createBackPropagationPass() {
  return new BackPropagationPass();
}
