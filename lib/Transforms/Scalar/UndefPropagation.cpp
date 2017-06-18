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
