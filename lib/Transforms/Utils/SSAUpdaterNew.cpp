//===- SSAUpdaterNew.cpp - Unstructured SSA Update Tool
//----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the SSAUpdaterNew class.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/SSAUpdaterNew.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/TinyPtrVector.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <utility>

using namespace llvm;

#define DEBUG_TYPE "SSAUpdaterNew"

SSAUpdaterNew::SSAUpdaterNew(SmallVectorImpl<PHINode *> *NewPHI)
    : InsertedPHIs(NewPHI) {}

SSAUpdaterNew::~SSAUpdaterNew() {}
void SSAUpdaterNew::setType(unsigned Var, Type *Ty) { CurrentType[Var] = Ty; }
void SSAUpdaterNew::setName(unsigned Var, StringRef Name) {
  CurrentName[Var] = Name;
}

// Store a def of Variable Var, in BB, with Value V
void SSAUpdaterNew::writeVariable(unsigned Var, BasicBlock *BB, Value *V) {
  CurrentDef[{Var, BB}] = V;
}

// Given a use that occurs after the most recent definition of a variable in a
// block, get the value of that use.
// IE
// def (foo)
// use (foo)
// You would use readVariableAfterDef after calling writeVariable for the def
Value *SSAUpdaterNew::readVariableAfterDef(unsigned Var, BasicBlock *BB) {
  auto CDI = CurrentDef.find({Var, BB});
  if (CDI != CurrentDef.end())
    return CDI->second;
  return readVariableBeforeDef(Var, BB);
}

// Given a use that occurs, currently, before the first definition of a
// variablein a block, get the value for that use.
// IE given
// use (foo)
// def (foo)
// You would use readVariableBeforeDef to get the value for the use of foo

// This is the marker algorithm from "Simple and Efficient Construction of
// Static Single Assignment Form"
// The simple, non-marker algorithm places phi nodes at any join
// Here, we place markers, and only place phi nodes if they end up necessary.
// They are only necessary if they break a cycle (IE we recursively visit
// ourselves again), or we discover, while getting the value of the operands,
// that there are two or more definitions needing to be merged.
// This still will leave non-minimal form in the case of irreducible control
// flow, where phi nodes may be in cycles with themselves, but unnecessary.
Value *SSAUpdaterNew::readVariableBeforeDef(unsigned Var, BasicBlock *BB) {
  Value *Result;

  // Single predecessor case, just recurse
  if (BasicBlock *Pred = BB->getSinglePredecessor()) {
    Result = readVariableAfterDef(Var, Pred);
  } else if (VisitedBlocks.count({Var, BB})) {
    // We hit our node again, meaning we had a cycle, we must insert a phi
    // node to break it.
    IRBuilder<> B(BB, BB->begin());
    Result = B.CreatePHI(CurrentType.lookup(Var), 0, CurrentName.lookup(Var));
  } else {
    // Mark us visited so we can detect a cycle
    VisitedBlocks.insert({Var, BB});
    SmallVector<Value *, 8> PHIOps;

    // Recurse to get the values in our predecessors. This will insert phi nodes
    // if we cycle
    for (auto *Pred : predecessors(BB))
      PHIOps.push_back(readVariableAfterDef(Var, Pred));
    // Now try to simplify the ops to avoid placing a phi.
    // This may return null if we never created a phi yet, that's okay
    PHINode *Phi = dyn_cast_or_null<PHINode>(CurrentDef.lookup({Var, BB}));
    // Check if the existing phi has the operands we need
    // It may be we placed due to a cycle, in which case, the number of operands
    // will be 0
    if (Phi && Phi->getNumOperands() != 0)
      if (!std::equal(Phi->op_begin(), Phi->op_end(), PHIOps.begin()))
        Phi = nullptr;
    Result = tryRemoveTrivialPhi(Var, Phi, PHIOps);
    // If we couldn't simplify, we may have to create a phi
    if (Result == Phi) {
      if (!Phi) {
        IRBuilder<> B(BB, BB->begin());
        Phi = B.CreatePHI(CurrentType.lookup(Var), 0, CurrentName.lookup(Var));
      }

      // These will be filled in by the recursive read.
      for (auto *Pred : predecessors(BB))
        Phi->addIncoming(CurrentDef.lookup({Var, Pred}), Pred);
      Result = Phi;
    }
    if (InsertedPHIs)
      if (PHINode *PN = dyn_cast<PHINode>(Result))
        InsertedPHIs->push_back(PN);
    // Set ourselves up for the next variable by resetting visited state.
    VisitedBlocks.erase({Var, BB});
  }
  writeVariable(Var, BB, Result);
  return Result;
}

// Recurse over a set of phi uses to eliminate the trivial ones
Value *SSAUpdaterNew::recursePhi(unsigned Var, Value *Phi) {
  if (!Phi)
    return nullptr;
  TrackingVH<Value> Res(Phi);
  SmallVector<TrackingVH<Value>, 8> Uses;
  std::copy(Phi->user_begin(), Phi->user_end(), std::back_inserter(Uses));
  for (auto &U : Uses) {
    if (PHINode *UsePhi = dyn_cast<PHINode>(&*U)) {
      auto OperRange = UsePhi->operands();
      tryRemoveTrivialPhi(Var, UsePhi, OperRange);
    }
  }
  return Res;
}

// Eliminate trivial phis
// Phis are trivial if they are defined either by themselves, or all the same
// argument.
// IE phi(a, a) or b = phi(a, b) or c = phi(a, a, c)
// We recursively try to remove
template <class RangeType>
Value *SSAUpdaterNew::tryRemoveTrivialPhi(unsigned Var, Instruction *Phi,
                                          RangeType &Operands) {
  // Detect equal or self arguments
  Value *Same = nullptr;
  for (auto &Op : Operands) {
    // If the same or self, good so far
    if (Op == Phi || Op == Same)
      continue;
    // not the same, return the phi since it's not eliminatable by us
    if (Same)
      return Phi;
    Same = Op;
  }
  // Never found a non-self reference, the phi is undef
  if (Same == nullptr)
    return UndefValue::get(CurrentType.lookup(Var));
  if (Phi) {
    Phi->replaceAllUsesWith(Same);
    Phi->eraseFromParent();
  }

  // We should only end up recursing in case we replaced something, in which
  // case, we may have made other Phis trivial.
  return recursePhi(Var, Same);
}

// Tarjan's algorithm with Nuutila's improvements
// Wish we could use SCCIterator, but graph traits makes it *very* hard to
// create induced subgraphs because it
// 1. only works on pointers, so i can't just create an intermediate struct
// 2. the functions are static, so i can't just override them in a subclass of
// graphtraits, or otherwise store state in the struct.

struct TarjanSCC {
  unsigned int DFSNum = 1;
  SmallPtrSet<Value *, 8> InComponent;
  DenseMap<Value *, unsigned int> Root;
  SmallPtrSet<Value *, 8> PHISet;
  SmallVector<Value *, 8> Stack;
  // Store the components as vector of ptr sets, because we need the topo order
  // of SCC's, but not individual member order
  SmallVector<SmallPtrSet<PHINode *, 8>, 8> Components;
  TarjanSCC(const SmallVectorImpl<PHINode *> &Phis)
      : PHISet(Phis.begin(), Phis.end()) {
    for (auto Phi : Phis)
      if (Root.lookup(Phi) == 0)
        FindSCC(Phi);
  }
  void FindSCC(PHINode *Phi) {
    Root[Phi] = ++DFSNum;
    // Store the DFS Number we had before it possibly gets incremented.
    unsigned int OurDFS = DFSNum;
    InComponent.erase(Phi);
    for (auto &PhiOp : Phi->operands()) {
      // Only inducing the subgraph of phis we got passed
      if (!PHISet.count(PhiOp))
        continue;
      if (Root.lookup(PhiOp) == 0)
        FindSCC(cast<PHINode>(PhiOp));
      if (!InComponent.count(PhiOp))
        Root[Phi] = std::min(Root.lookup(Phi), Root.lookup(PhiOp));
    }
    // See if we really were the root, by seeing if we still have our DFSNumber,
    // or something lower
    if (Root.lookup(Phi) == OurDFS) {
      Components.resize(Components.size() + 1);
      auto &Component = Components.back();
      Component.insert(Phi);
      DEBUG(dbgs() << "Component root is " << *Phi << "\n");
      InComponent.insert(Phi);
      while (!Stack.empty() && Root.lookup(Stack.back()) >= OurDFS) {
        DEBUG(dbgs() << "Component member is " << *Stack.back() << "\n");
        Component.insert(cast<PHINode>(Stack.back()));
        InComponent.insert(Stack.back());
        Stack.pop_back();
      }
    } else {
      // Part of a component, push to stack
      Stack.push_back(Phi);
    }
  }
};

// Condense the set of SCCs and by extension, necessary phis
void SSAUpdaterNew::processSCC(const SmallPtrSetImpl<PHINode *> &Component) {
#ifndef NDEBUG
  DEBUG(dbgs() << "Start component\n");
  for (auto *Member : Component)
    DEBUG(dbgs() << "Component member is " << *Member << "\n");
  DEBUG(dbgs() << "End component\n");
#endif

  // We already processed trivial components
  if (Component.size() == 1)
    return;

  SmallVector<PHINode *, 8> Inner;
  SmallPtrSet<Value *, 8> OuterOps;

  // See which members have operands inside or outside our component.
  for (auto *Phi : Component) {
    bool isInner = true;
    for (auto &PhiOp : Phi->operands())
      if (!isa<PHINode>(PhiOp) || !Component.count(cast<PHINode>(PhiOp))) {
        OuterOps.insert(PhiOp);
        isInner = false;
      }
    if (isInner)
      Inner.push_back(Phi);
  }
  // If there is only one outside operand, all the phis end up resolving to that
  // value.
  // If there is more than one outside operand, then the ones with outside
  // operands are necessary.  We then condense the set to the nodes only having
  // inner ops. Because Tarjan's SCC algorithm is maximal, we may be able to
  // reduce these even further.
  if (OuterOps.size() == 1) {
    Value *Replacement = *OuterOps.begin();
    for (auto *Member : Component) {
      // FIXME: Speed this up
      auto Iter = std::find(InsertedPHIs->begin(), InsertedPHIs->end(), Member);
      if (Iter != InsertedPHIs->end()) {
        // swap to the end and resize, to avoid erase in middle
        std::swap(*Iter, InsertedPHIs->back());
        InsertedPHIs->resize(InsertedPHIs->size() - 1);
      }

      Member->replaceAllUsesWith(Replacement);
      Member->eraseFromParent();
    }
  } else if (OuterOps.size() > 1) {
    minimizeInsertedPhisHelper(Inner);
  }
}

void SSAUpdaterNew::minimizeInsertedPhisHelper(
    const SmallVectorImpl<PHINode *> &Phis) {
  if (Phis.empty())
    return;
  // Compute the induced subgraph
  TarjanSCC SCCFinder(Phis);
  for (auto &Component : SCCFinder.Components) {
    processSCC(Component);
  }
}

void SSAUpdaterNew::minimizeInsertedPhis() {
  if (!InsertedPHIs)
    return;

  minimizeInsertedPhisHelper(*InsertedPHIs);
}
