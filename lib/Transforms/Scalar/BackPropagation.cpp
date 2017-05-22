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
#include "llvm/Transforms/Utils/Local.h"

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
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

  inline bool operator==(const PropagatedInfo &RHS) const {
    return IgnoreSign == RHS.IgnoreSign;
  }
  inline bool operator!=(const PropagatedInfo &RHS) const {
    return !(*this == RHS);
  }
};

class BackPropagationImpl {
  Function &F;

  // List of Visited blocks in the first post-order traversal of
  // the function. We use it to identify unprocessed PHI nodes.
  // FIXME: should this be a BitVector?
  SmallPtrSet<BasicBlock *, 8> VisitedBlocks;

  // Keeps the mapping between Instruction and propagation info.
  DenseMap<Instruction *, PropagatedInfo *> InstructionToInfo;

  // Worklist of instruction for processing.
  SmallSetVector<Instruction *, 16> WorkList;

  // List of "interesting" DEFs + propagation info sorted in post-order.
  SmallVector<std::pair<Instruction *, PropagatedInfo *>, 16> InstructionsPO;

  // Bump pointer allocator to allocate propagation info.
  BumpPtrAllocator PIAlloc;

  void processInstruction(Instruction &);
  void processUse(Use &, PropagatedInfo &);
  void reprocessInputs(Instruction &I);

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

void BackPropagationImpl::reprocessInputs(Instruction &I) {
  for (Use &U : I.uses())
    if (auto *UI = dyn_cast<Instruction>(U.get()))
      WorkList.insert(UI);
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

  if (!Interesting) {
    // The information we found is not interesting for propagation.
    // If we has something already in the map, we need to remove it,
    // and reprocess all the uses.
    if (InstructionToInfo.count(&I)) {
      DEBUG(dbgs() << "Removing PropagatedInfo for: " << I << "\n");
      InstructionToInfo.erase(&I);
      reprocessInputs(I);
      return;
    }

    // Even if the value wasn't in the map, and this is a PHI, we
    // need to reprocess as we optimistically ignored values carried
    // by backedges.
    if (isa<PHINode>(&I))
      reprocessInputs(I);
    return;
  }

  if (!InstructionToInfo.count(&I)) {
    // This is the first time we see this DEF.
    auto *InfoPtr = new (PIAlloc) PropagatedInfo(true /* Optimistic */);
    InstructionToInfo[&I] = InfoPtr;
    InstructionsPO.push_back({&I, InfoPtr});

    // If this is a PHINode, we need to reprocess backedge uses,
    // as we ignored them in the first place and our optimistic
    // hypothesis could be wrong.
    if (isa<PHINode>(I))
      reprocessInputs(I);
  } else {
    // We could've found that our information is still useful
    // but differs from the one we had before. This means we've
    // been too optimistic so a refinement is needed.
    PropagatedInfo *OldPI = InstructionToInfo[&I];
    if (*OldPI != PI) {
      DEBUG(dbgs() << "Updating PropagatedInfo for: " << I << "\n");
      *OldPI = PI;
    }
  }
}

bool BackPropagationImpl::runBackProp() {
  bool Changed = false;
  PostOrderTraversal<Function *> POT(&F);

#ifndef NDEBUG
  for (auto &BB : POT) {
    DEBUG(dbgs() << "Dumping BB: "
                 << "\n");
    DEBUG(dbgs() << BB << "\n");
  }
#endif

  // Step 1: Walk the function in post-order, and walk each
  // BasicBlock in the reverse direction (last-to-first instruction).
  // Optimistically ignore values carried by backedges in PHI(s).
  for (auto &BB : POT) {
    for (auto &I : reverse(*BB))
      processInstruction(I);

    // Mark this block as processed.
    VisitedBlocks.insert(BB);
  }

  // Step 2: Refine our hyphotesis until we hit a maximal fixpoint.
  while (!WorkList.empty()) {
    Instruction *I = WorkList.pop_back_val();
    DEBUG(dbgs() << "Processing instruction: " << *I << "\n");
    processInstruction(*I);
  }

  // Step 3: Walk the "potentially" interesting values in reverse post
  // order, filtering those that are not interesting anymore, and propagate
  // informations USE(s)->DEF(s).
  // FIXME: I wanted to use `make_filter_range` but that returns an
  // unidirectional iterator so I can't walk it the other way around.
  for (auto &Info : reverse(InstructionsPO)) {
    if (Info.second->canUseInfo())
      continue;
  }

  // Step 4: Another post order walk, to remove now dead instructions.
  for (auto &Info : InstructionsPO) {
    Instruction *I = Info.first;
    if (isInstructionTriviallyDead(I)) {
      I->eraseFromParent();
      Changed = true;
    }
  }

  return Changed;
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
