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

#include "llvm/IR/Function.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

#define DEBUG_TYPE "undefprop"

struct TarjanSCC {

  TarjanSCC() : Components(1) {}

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

private:
  void FindSCC(const Instruction *I) {
    Root[I] = ++DFSNum;
    // Store the DFS Number we had before it possibly gets incremented.
    unsigned int OurDFS = DFSNum;
    for (auto &Op : I->operands()) {
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
  DenseMap<const Value *, unsigned int> Root;
  SmallVector<const Value *, 8> Stack;
  // Store the components as vector of ptr sets, because we need the topo order
  // of SCC's, but not individual member order
  SmallVector<SmallPtrSet<const Value *, 8>, 8> Components;
  DenseMap<const Value *, unsigned> ValueToComponent;
};

class UndefPropagationPass : public FunctionPass {
public:
  void getAnalysisUsage(AnalysisUsage &AU) const override {}

  static char ID; // Pass identification, replacement for typeid

  UndefPropagationPass() : FunctionPass(ID) {
    initializeUndefPropagationPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override {
    if (skipFunction(F))
      return false;
    return false;
  }
};

char UndefPropagationPass::ID = 0;
INITIALIZE_PASS_BEGIN(UndefPropagationPass, "undefprop",
                      "Propagate undef over the SSA graph", false, false)
INITIALIZE_PASS_END(UndefPropagationPass, "undefprop",
                    "Propagate undef over the SSA graph", false, false)

// chis is the public interface to this file.
FunctionPass *llvm::createUndefPropagationPass() {
  return new UndefPropagationPass();
}
