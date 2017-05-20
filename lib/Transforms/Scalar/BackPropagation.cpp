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

#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

#define DEBUG_TYPE "backprop"

namespace {
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
    return false;
  }
};
} // end anonymous namespace

char BackPropagationPass::ID = 0;
INITIALIZE_PASS_BEGIN(BackPropagationPass, "backprop",
                      "Backpropagation of informations", false, false)
INITIALIZE_PASS_END(BackPropagationPass, "backprop",
                    "BackPropagation of informations", false, false)

// chis is the public interface to this file.
FunctionPass *llvm::createBackPropagationPass() {
  return new BackPropagationPass();
}
