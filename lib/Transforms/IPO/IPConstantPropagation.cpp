//===-- IPConstantPropagation.cpp - Propagate constants through calls -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass implements an _extremely_ simple interprocedural constant
// propagation pass.  It could certainly be improved in many different ways,
// like using a worklist.  This pass makes arguments dead, but does not remove
// them.  The existing dead argument elimination pass should be run after this
// to clean up the mess.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/JumpFunctions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
using namespace llvm;

#define DEBUG_TYPE "ipconstprop"

namespace {
  /// IPCP - The interprocedural constant propagation pass
  ///
  struct IPCP : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    IPCP() : ModulePass(ID) {
      initializeIPCPPass(*PassRegistry::getPassRegistry());
    }

    bool runOnModule(Module &M) override;
    void getAnalysisUsage(AnalysisUsage &AU) const override;

    // Interprocedural transform entry point.
    bool performIPCP(Module &, CallGraph &, JumpFunctionAnalysis &);

    // Intra-SCC solver.
    void solveForSingleSCC(Function *F, JumpFunctionAnalysis &JFA);

    // Returns true if the two functions passed as arguments are
    // in the same strongly connected component.
    bool inTheSameSCC(Function *F1, Function *F2);

private:
    DenseMap<Function *, unsigned> SCCNumberMap;
  };
}

char IPCP::ID = 0;
INITIALIZE_PASS(IPCP, "ipconstprop",
                "Interprocedural constant propagation", false, false)

ModulePass *llvm::createIPConstantPropagationPass() { return new IPCP(); }

bool IPCP::inTheSameSCC(Function *F1, Function *F2) {
  assert(F1 && F2 && "isTheSameSCC called on invalid functions!");
  assert(SCCNumberMap.count(F1) == 1 && SCCNumberMap.count(F2) == 1 &&
         "Functions not belonging to any SCC!");
  return SCCNumberMap[F1] == SCCNumberMap[F2];
}

void IPCP::solveForSingleSCC(Function *F, JumpFunctionAnalysis &JFA) {
  for (auto *U : F->users()) {
    auto *I = dyn_cast<Instruction>(U);
    if (!I)
      return;
    CallSite CS(I);
    if (!CS)
      return;

    // We hit an edge across SCCs, don't propagate.
    Function *Callee = CS.getCalledFunction();
    if (!inTheSameSCC(F, Callee))
      continue;

    std::vector<JumpFunction> Funcs = JFA.getJumpFunctionForCallSite(CS);
    unsigned ArgNo = 0;
    for (JumpFunction &F : Funcs) {
#if 0
      meetWith();
#endif
      ArgNo++;
    }
  }
}

bool IPCP::performIPCP(Module &M, CallGraph &CG, JumpFunctionAnalysis &JFA) {
  SmallVector<Function *, 32> Worklist;
  unsigned SCCNo = 0;

  for (scc_iterator<CallGraph *> I = scc_begin(&CG); !I.isAtEnd(); ++I) {

    // LLVM only provides a post-order SCC traversal, which gives a topo order
    // callee -> caller. Here we want an RPO traversal, which gives us a
    // caller -> callee ordering, as we want to propagate constant arguments
    // from calls to arguments. So, we take the SCC roots in PO and we iterate
    // them in reverse.
    Function *F = I->front()->getFunction();
    if (F && !F->isDeclaration())
      Worklist.push_back(F);

    // We do two kind of propagation: within an SCC (intra), and across SCCs
    // (inter). Here we build a map from functions to SCC numbers so that we
    // can find out which edges span across strongly connected components.
    for (CallGraphNode *CGN : *I) {
      Function *F = CGN->getFunction();
      if (F && !F->isDeclaration()) {
        assert(!SCCNumberMap.count(F) && "Function already visited!");
        SCCNumberMap[F] = SCCNo;
      }
    }

    SCCNo++;
  }

  for (Function *F : reverse(Worklist))
    solveForSingleSCC(F, JFA);
  return false;
}

bool IPCP::runOnModule(Module &M) {
  if (skipModule(M))
    return false;

  CallGraph &CG = getAnalysis<CallGraphWrapperPass>().getCallGraph();
  JumpFunctionAnalysis &JFA = getAnalysis<JumpFunctionsWrapperPass>().getJumpFunctions();
  return performIPCP(M, CG, JFA);
}

void IPCP::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<CallGraphWrapperPass>();
  AU.addRequired<JumpFunctionsWrapperPass>();
}
