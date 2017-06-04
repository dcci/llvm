//===- JumpFunctions.cpp - Compute Jump Functions  ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Add a description here.
//
//===----------------------------------------------------------------------===//

#include "llvm/Analysis/JumpFunctions.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
using namespace llvm;

#define DEBUG_TYPE "jump-functions"

char JumpFunctionsWrapperPass::ID = 0;
INITIALIZE_PASS_BEGIN(JumpFunctionsWrapperPass, "jump-functions",
                      "Compute Jump Functions for module", false, true);
INITIALIZE_PASS_END(JumpFunctionsWrapperPass, "jump-functions",
                    "Compute Jump Functions for module", false, true);

JumpFunctionsWrapperPass::JumpFunctionsWrapperPass() : ModulePass(ID) {
  initializeJumpFunctionsWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool JumpFunctionsWrapperPass::runOnModule(Module &M) { return false; }

void JumpFunctionsWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
#if 0
	AU.addRequired<CallGraphWrapperPass>();
#endif
}
