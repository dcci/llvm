//===------ UndefProp.cpp - Propagate undef over the SSA graph ------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Describe the algorithm.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/SetVector.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

#define DEBUG_TYPE "undefprop"

struct UseDefSCC {
  UseDefSCC() {}

  void Start(const Instruction *Start) {
    if (Root.lookup(Start) == 0)
      FindSCC(Start);
  }

  const SmallPtrSetImpl<const Value *> &getComponentFor(const Value *V) const {
    unsigned ComponentID = ValueToComponent.lookup(V);

    assert(ComponentID > 0 &&
           "Asking for a component for a value we never processed");
    return Components[ComponentID];
  }

  // Store the components as vector of ptr sets, because we need the topo order
  // of SCC's, but not individual member order
  SmallVector<SmallPtrSet<const Value *, 8>, 8> Components;
  DenseMap<const Value *, unsigned> ValueToComponent;
  DenseMap<const Value *, unsigned int> Root;

private:
  void FindSCC(const Instruction *I) {
    Root[I] = ++DFSNum;
    // Store the DFS Number we had before it possibly gets incremented.
    unsigned int OurDFS = DFSNum;
    for (auto *Op : I->users()) {
      if (auto *InstOp = dyn_cast<Instruction>(Op)) {
        if (Root.lookup(Op) == 0)
          FindSCC(InstOp);
        if (!InComponent.count(Op))
          Root[I] = std::min(Root.lookup(I), Root.lookup(Op));
      }
    }
    // See if we really were the root of a component, by seeing if we still have
    // our DFSNumber.  If we do, we are the root of the component, and we have
    // completed a component. If we do not, we are not the root of a component,
    // and belong on the component stack.
    if (Root.lookup(I) == OurDFS) {
      unsigned ComponentID = Components.size();
      Components.resize(Components.size() + 1);
      auto &Component = Components.back();
      Component.insert(I);
      DEBUG(dbgs() << "Component root is " << *I << "\n");
      InComponent.insert(I);
      ValueToComponent[I] = ComponentID;
      // Pop a component off the stack and label it.
      while (!Stack.empty() && Root.lookup(Stack.back()) >= OurDFS) {
        auto *Member = Stack.back();
        DEBUG(dbgs() << "Component member is " << *Member << "\n");
        Component.insert(Member);
        InComponent.insert(Member);
        ValueToComponent[Member] = ComponentID;
        Stack.pop_back();
      }
    } else {
      // Part of a component, push to stack
      Stack.push_back(I);
    }
  }
  unsigned int DFSNum = 1;
  SmallPtrSet<const Value *, 8> InComponent;
  SmallVector<const Value *, 8> Stack;
};

class UndefLattice {
private:
  enum { Top, Undef, Bottom } LatticeState;

public:
  UndefLattice() : LatticeState(Top) {}
  bool isTop() { return LatticeState == Top; };
  bool isUndef() { return LatticeState == Undef; }
  bool isBottom() { return LatticeState == Bottom; }

  bool setBottom() {
    if (LatticeState != Bottom) {
      LatticeState = Bottom;
      return true;
    }
    return false;
  }

  // Meet operation.
  // This function returns true if the state of the lattice change,
  // i.e. if we go down the lattice. It's not possible to go up lattice as
  // that would break monotoniticy.
  bool meet(Value *V) {
    // This lattice is already in the bottom state, it doesn't matter what we're
    // trying to meet with.
    if (LatticeState == Bottom)
      return false;
    // The meet rule for Top is: top meet something = something.
    //  i.e.
    //    -> Top meet undef = undef
    //    -> Top meet Bottom = Bottom
    if (LatticeState == Top) {
      if (isa<UndefValue>(V))
        LatticeState = Undef;
      else
        LatticeState = Bottom;
      return true;
    }

    // If this is a constant, we only remain a constant if the new value we
    // meet with is the same we have. Otherwise we do all the way down to
    // bottom.
    if (LatticeState == Undef) {
      if (isa<UndefValue>(V))
        return false;
      LatticeState = Bottom;
      return true;
    }
    llvm_unreachable("Unhandled lattice transition!");
  }

  // Variant of meet taking a lattice value.
  bool meet(UndefLattice L) {
    if (LatticeState == Bottom)
      return false;
    if (LatticeState == Top) {
      if (L.isUndef())
        LatticeState = Undef;
      else
        LatticeState = Bottom;
      return true;
    }
    if (LatticeState == Undef) {
      if (L.isUndef() == Undef)
        return false;
      LatticeState = Bottom;
      return true;
    }
    llvm_unreachable("Unhandled lattice transition!");
  }
};

class UndefPropagationPass : public FunctionPass {
  using EdgesVector =
      SmallSetVector<std::pair<const Instruction *, const Instruction *>, 8>;

public:
  void getAnalysisUsage(AnalysisUsage &AU) const override {}

  static char ID;

  UndefPropagationPass() : FunctionPass(ID) {
    initializeUndefPropagationPassPass(*PassRegistry::getPassRegistry());
  }

  // FIXME: add comments to the class.
  bool propagateUndef(Function &);
  void processSCC(SmallPtrSet<const Value *, 8> &, EdgesVector &);
  void processInterSCC(EdgesVector &);
  bool processPHI(const PHINode *);
  bool processInstruction(const Instruction *);

  UndefLattice &getLatticeFor(const Instruction *I) {
    assert(LatticeMap.count(I) && "This instruction is not in the map!");
    return LatticeMap[I];
  }

  DenseMap<const Instruction *, UndefLattice> &getLatticeMap() {
    return LatticeMap;
  }

  bool runOnFunction(Function &F) override {
    if (skipFunction(F))
      return false;
    return propagateUndef(F);
  }

private:
  bool areInTheSameSCC(const Instruction *, const Instruction *);

  UseDefSCC SCCFinder;
  DenseMap<const Instruction *, UndefLattice> LatticeMap;
  EdgesVector InterSCCEdges;
};

bool UndefPropagationPass::processPHI(const PHINode *Phi) {
  UndefLattice &L = getLatticeFor(Phi);

  // Look at all the arguments of this PHINode.
  // We have some cases to keep in mind:
  //  1) If any of the arguments varies or two arguments are constant and
  //     disagree on the value, then we can't do anything with this PHI.
  //  2) If we have just one constant value (`undef`) and the other arguments
  //     are still unresolved we can optimistically propagate undef to the
  //     users and then refine our hyphotesis later if we find it wrong.
  if (llvm::all_of(Phi->operands(), [](Value *Arg) {
        if (isa<Constant>(Arg) && isa<UndefValue>(Arg))
          return true;
        return false;
      })) {
    Value *Arg0 = Phi->getOperand(0);
    return L.meet(Arg0);
  }

  // This is really pessimistic. We should do better.
  return L.setBottom();
}

bool UndefPropagationPass::processInstruction(const Instruction *I) {
  UndefLattice &L = getLatticeFor(I);

  // Currently handling only binary operations, will grow support for other
  // ops in the future.
  if (!I->isBinaryOp())
    return L.setBottom();

  // FIXME: create once and use it everywhere.
  DataLayout DL = I->getParent()->getParent()->getParent()->getDataLayout();
  SimplifyQuery SQ(DL);

  // Look at the lattice values associated with the operands and see if we can
  // use them to propagate some information.
  auto getLatticeUndef = [this](Instruction *I) -> Value * {
    if (I) {
      UndefLattice &L = getLatticeFor(I);
      if (L.isUndef())
        return UndefValue::get(I->getType());
    }
    return nullptr;
  };
  auto *Op0 = dyn_cast<Instruction>(I->getOperand(0));
  auto *Op1 = dyn_cast<Instruction>(I->getOperand(1));
  if (Op0 || Op1) {
    Value *V1 = getLatticeUndef(Op0);
    Value *V2 = getLatticeUndef(Op1);
    Value *Simplified =
        SimplifyBinOp(I->getOpcode(), V1 ? V1 : I->getOperand(0),
                      V2 ? V2 : I->getOperand(1), SQ);
    if (Simplified && isa<UndefValue>(Simplified))
      return L.meet(Simplified);
  }

  // This binary operation could have just two constants as operands,
  // e.g. :
  //   %tinky = add nsw i32 undef, 1
  // which folds to undef.
  // So we want to give a shot to the constant folder to give us something.
  auto *C0 = dyn_cast<Constant>(I->getOperand(0));
  auto *C1 = dyn_cast<Constant>(I->getOperand(1));
  if (C0 && C1) {
    Value *Simplified = ConstantExpr::get(I->getOpcode(), C0, C1);
    if (Simplified && isa<UndefValue>(Simplified))
      return L.meet(Simplified);
  }

  return L.setBottom();
}

// Probably this should live inside the SCC finder, although I didn't want
// to diverge fundamentally from the version of the SCC finder in NewGVN.
bool UndefPropagationPass::areInTheSameSCC(const Instruction *I1,
                                           const Instruction *I2) {
  auto &Root = SCCFinder.Root;
  assert(Root.count(I1) && Root.count(I2) &&
         "Instructions don't belong to any strongly connected component!");
  return Root[I1] == Root[I2];
}

void UndefPropagationPass::processSCC(SmallPtrSet<const Value *, 8> &Component,
                                      EdgesVector &InterSCCEdges) {
  DEBUG(dbgs() << "Processing SCC members\n");

  // Here we use a SmallSetVector for two reasons:
  // 1) We don't have to worry about keeping track wheter an element has been
  //    already inserted or not in the Worklist, getting set-like insert
  //    semantic "for free".
  // 2) We expect the size of a single SCC in the SSA graph to be small enough
  //    that the worklist operations never trigger allocations.
  SmallSetVector<const Instruction *, 8> Worklist;

  for (auto *Node : Component) {
    auto *I = dyn_cast<Instruction>(Node);
    assert(I && "Nodes of an SCC should be instructions!");
    Worklist.insert(I);
  }

  while (!Worklist.empty()) {
    const Instruction *I = Worklist.pop_back_val();
    bool Changed = false;
    DEBUG(dbgs() << "Popping from worklist: " << *I << "\n");

    // Here we do intra-SCC propagation of facts. We use a simple
    // worklist algorithm that propagates fact within the SCC until
    // we hit fixpoint. As SCCs are small in real-world programs
    // this should converge really quickly without fancier visitation
    // strategies, although one can prove that you can do better.
    if (isa<PHINode>(I))
      Changed = processPHI(cast<const PHINode>(I));
    else
      Changed = processInstruction(I);

    // OK, we found out something changed, i.e. we had a transition down
    // the lattice. Propagate to all the users of the instruction *within*
    // this SCC the information, and push them on the worklist to be
    // re-examined. Also remember the edges flowing from this SCC to another
    // so once we're done examining the SCC we can use it to propagate
    // the information inter-SCC.
    if (Changed) {
      UndefLattice &LI = getLatticeFor(I);
      for (auto *U : I->users()) {
        auto *UI = dyn_cast<Instruction>(U);
        if (!UI)
          continue;
        if (!areInTheSameSCC(I, UI)) {
          InterSCCEdges.insert({I, UI});
          continue;
        }
        UndefLattice &LI2 = getLatticeFor(UI);
        Changed = LI2.meet(LI);
        if (Changed)
          Worklist.insert(UI);
      }
    }
  }
  DEBUG(dbgs() << "End processing SCC\n");
}

void UndefPropagationPass::processInterSCC(EdgesVector &InterSCCEdges) {
  for (auto Pair : InterSCCEdges) {
    const Instruction *I1 = Pair.first;
    const Instruction *I2 = Pair.second;
    assert(I1 && I2 && "Broken edge between SCCs!");
    UndefLattice &L1 = getLatticeFor(I1);
    UndefLattice &L2 = getLatticeFor(I2);
    L2.meet(L1);
  }
}

bool UndefPropagationPass::propagateUndef(Function &F) {
  bool Changed = false;

  // FIMXE: only look at the induced subgraph on undef.
  for (const Instruction &I : instructions(F)) {
    LatticeMap[&I] = UndefLattice();
    SCCFinder.Start(&I);
  }

  // SCCs are inherently discovered in post-order, but we want
  // RPO, so we iterate the components vector in reverse order.
  for (auto &Component : reverse(SCCFinder.Components)) {
    InterSCCEdges.clear();
    processSCC(Component, InterSCCEdges);

    // Now that a single SCC converged, try to propagate to the next SCC.
    processInterSCC(InterSCCEdges);
  }

  // We're done solving. Now replace what we found being constant across
  // the SSA graph and call it a night.
  for (auto &KV : getLatticeMap()) {
    if (KV.second.isUndef()) {
      Instruction *I = const_cast<Instruction *>(KV.first);
      DEBUG(dbgs() << "Found undef: " << *I << "\n");
      I->replaceAllUsesWith(UndefValue::get(I->getType()));
      if (!I->mayHaveSideEffects())
        I->eraseFromParent();
      Changed = true;
    }
  }

  return Changed;
}

char UndefPropagationPass::ID = 0;
INITIALIZE_PASS_BEGIN(UndefPropagationPass, "undefprop",
                      "Propagate undef over the SSA graph", false, false)
INITIALIZE_PASS_END(UndefPropagationPass, "undefprop",
                    "Propagate undef over the SSA graph", false, false)

// This is the public interface to this file.
FunctionPass *llvm::createUndefPropagationPass() {
  return new UndefPropagationPass();
}
