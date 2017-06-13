//===-- IPConstantPropagation.cpp - Propagate constants through calls -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Add a real description here.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/IPO.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/JumpFunctions.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
using namespace llvm;

#define DEBUG_TYPE "ipconstprop"

#define MYDEBUG // FIXME: this needs to go away.

namespace {
// We should really factor this code out and share with SCCP.
// SCCP currently uses a 4 state lattice (including forcedConstant)
// because of `undef` oddities, but once that's fixed this code
// will go away.
class Lattice {
private:
  enum { Top, Constant, Bottom } LatticeState;

  Value *LatticeConstant = nullptr;

public:
  Lattice() : LatticeState(Top) {}
  bool isTop() { return LatticeState == Top; };
  bool isConstant() { return LatticeState == Constant; }
  Value *getConstant() { return LatticeConstant; }
  bool isBottom() { return LatticeState == Bottom; }

  // Meet operation of the current lattice value with the value of the jump
  // function. This function returns true if the state of the lattice change,
  // i.e. if we go down the lattice. It's not possible to go up lattice as
  // that would break monotoniticy.
  bool meet(JumpFunction &Func) {
    // This lattice is already in the bottom state, it doesn't matter what we're
    // trying to meet with.
    if (LatticeState == Bottom)
      return false;

    // The meet rule for Top is: top meet something = something.
    //  i.e.
    //    -> Top meet costant = constant
    //    -> Top meet Bottom = Bottom
    if (LatticeState == Top) {
      if (Func.isConstant()) {
        LatticeConstant = Func.getConstant();
        LatticeState = Constant;
      } else if (Func.isUnknown()) {
        LatticeState = Bottom;
      } else {
        llvm_unreachable("Unhandled jump function state!");
      }
      return true;
    }

    // If this is a constant, we only remain a constant if the new value we
    // meet with is the same we have. Otherwise we do all the way down to
    // bottom.
    if (LatticeState == Constant) {
      if (Func.isConstant() && Func.getConstant() == LatticeConstant)
        return false;
      assert(Func.isUnknown() && "Unhandld jump function state!");
      LatticeState = Bottom;
      return true;
    }
    llvm_unreachable("Unhandled lattice transition!");
  }
};

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
  // We number SCCs when we walk them in post-order. This data
  // structure keeps track of the mapping between Functions within
  // an SCC and SCC number. We use this to find out whether two functions
  // share an SCC. Ideally this information should be available when
  // we do a CallGraph analysis instead of having analyses recomputing it.
  DenseMap<Function *, unsigned> SCCNumberMap;

  // Map from function arguments to lattices. We assign a lattice to each
  // of the function arguments and we lower informations every time we
  // acquire new informations about an argument.
  DenseMap<Argument *, Lattice> LatticeMap;
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

// Initially push the root of the SCC on the worklist, and analyze.
// If we end up discovering something, put the function we propagated the
// information to, and repeat until we converge. If we find an edge that
// crosses two SCCs, ignore propagatin facts, as we're interested only in
// intra-SCC propagation in this phase of the algorithm.
void IPCP::solveForSingleSCC(Function *Root, JumpFunctionAnalysis &JFA) {
  unsigned NumIterations = 0;
  SmallVector<Function *, 8> SCCWorkList;
  SmallPtrSet<Function *, 8> Visited;
  SCCWorkList.push_back(Root);
  Visited.insert(Root);

  while (!SCCWorkList.empty()) {
    // Keep track of the number of iterations needed to converge. If we're
    // iterating too much, that could be a symptom of fixpointing issues, so
    // we assert for safety. In practice, i.e. for real programs this should
    // converge pretty quickly. In the future, we can turn this into a
    // statistic.
    NumIterations += 1;
    assert(NumIterations < 1000 && "We processed the same SCC a lot");

    Function *F = SCCWorkList.pop_back_val();
    for (Instruction &I : instructions(F)) {
      auto *CI = dyn_cast<CallInst>(&I);
      if (!CI)
        continue;
      CallSite CS(CI);
      if (!CS)
        continue;

      Function *Callee = CS.getCalledFunction();

      // Guard against recursion.
      if (F == Callee)
        continue;

      if (!inTheSameSCC(F, Callee))
        continue;

      std::vector<JumpFunction> Funcs = JFA.getJumpFunctionForCallSite(CS);
      unsigned ArgNo = 0;
      bool Changed = false;
      for (Function::arg_iterator I = Callee->arg_begin(),
                                  E = Callee->arg_end();
           I != E; ++I) {
        Argument *Arg = &*I;
        assert(LatticeMap.count(Arg) &&
               "No lattice associated to this argument");
        Lattice &L = LatticeMap[Arg];
        Changed |= L.meet(Funcs[ArgNo]);
        ArgNo++;
      }
      if (Changed) {
        SCCWorkList.push_back(Callee);
        continue;
      }
      // There's probably a better way of doing this that doesn't involve
      // maintaining a separate set.
      if (!Visited.count(Callee)) {
        SCCWorkList.push_back(Callee);
        Visited.insert(Callee);
        continue;
      }
    }
  }
}

bool IPCP::performIPCP(Module &M, CallGraph &CG, JumpFunctionAnalysis &JFA) {
  // Initialize a lattice element for each of the arguments of the function
  // in the module. Maybe we could do that lazily as some functions can never
  // be called, but this doesn't seem to be a big compile time sink, so let's
  // keep it simple for now.
  for (Function &F : M) {
    for (Function::arg_iterator I = F.arg_begin(), E = F.arg_end(); I != E;
         ++I) {
      Argument *Arg = &*I;
      assert(!LatticeMap.count(Arg) &&
             "A lattice for this argument was already created");
      LatticeMap[Arg] = Lattice();
    }
  }

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

#ifdef MYDEBUG
  for (auto &KV : LatticeMap) {
    llvm::errs() << "Arg: " << *KV.first << "\n";
    Lattice L = KV.second;
    if (L.isTop())
      llvm::errs() << "Top";
    if (L.isConstant())
      llvm::errs() << "Constant: " << *(L.getConstant());
    if (L.isBottom())
      llvm::errs() << "Bottom";
    llvm::errs() << "\n";
  }
#endif

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
