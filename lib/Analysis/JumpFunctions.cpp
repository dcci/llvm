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
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
using namespace llvm;

#define DEBUG_TYPE "jump-functions"

JumpFunctionAnalysis::JumpFunctionAnalysis(Module &M, CallGraph &CG)
    : M(M), CG(CG) {
  computeJumpFunctions();
}

void JumpFunctionAnalysis::analyzeParamsInBasicBlock(BasicBlock &BB) {
}

void JumpFunctionAnalysis::createJumpFunction(CallSite *CS, Value *Operand,
                                             unsigned ArgPosition) {
  // We don't deal with aggregates for now.
  if (Operand->getType()->getScalarType())
    return;
  if (!isa<Constant>(Operand))
    return;
}

void JumpFunctionAnalysis::computeJumpFunctionForBasicBlock(BasicBlock &BB) {
  for (Instruction &I : BB) {
    auto *CI = dyn_cast<CallInst>(&I);
    if (!CI || CI->getNumOperands() == 0)
      continue;
    auto *CS = new CallSite(CI);
    unsigned ArgPos = 0;
    for (Value *Op : I.operands()) {
      createJumpFunction(CS, Op, ArgPos);
      ArgPos++;
    }
  }
}

void JumpFunctionAnalysis::analyzeFunction(Function &F) {
  auto DT = DominatorTree(F);
  for (auto DTN : depth_first(DT.getRootNode())) {
    BasicBlock *BB = DTN->getBlock();
    analyzeParamsInBasicBlock(*BB);
    computeJumpFunctionForBasicBlock(*BB);
  }
}

void JumpFunctionAnalysis::computeJumpFunctions() {
  for (Function &F : M)
    analyzeFunction(F);
}

char JumpFunctionsWrapperPass::ID = 0;
INITIALIZE_PASS_BEGIN(JumpFunctionsWrapperPass, "jump-functions",
                      "Compute Jump Functions for module", false, true);
INITIALIZE_PASS_END(JumpFunctionsWrapperPass, "jump-functions",
                    "Compute Jump Functions for module", false, true);

JumpFunctionsWrapperPass::JumpFunctionsWrapperPass() : ModulePass(ID) {
  initializeJumpFunctionsWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool JumpFunctionsWrapperPass::runOnModule(Module &M) {
  JumpFuncs.reset(new JumpFunctionAnalysis(
      M, getAnalysis<CallGraphWrapperPass>().getCallGraph()));
  return false;
}

void JumpFunctionsWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
	AU.addRequired<CallGraphWrapperPass>();
}
