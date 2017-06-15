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

JumpFunctionAnalysis::JumpFunctionAnalysis(Module &M) : M(M) {
  computeJumpFunctions();
}

void JumpFunctionAnalysis::print(raw_ostream &OS) const {
  OS << "Jump Function informations:\n";
  for (auto &KV : JumpFunctionMap) {
    CallSite CS = KV.first;
    std::vector<JumpFunction> JumpFuncs = KV.second;
    OS << "Callsite: " << *CS.getInstruction() << "\n";
    OS << "Jump functions\n";
    unsigned ArgNo = 0;
    for (JumpFunction &Func : JumpFuncs) {
      OS << "Arg " << ArgNo << " ";
      if (Func.isConstant()) {
        OS << "constant ";
        OS << *Func.getConstant();
      } else if (Func.isUnknown()) {
        OS << "unknown ";
      }
      OS << "\n";
      ArgNo++;
    }
    OS << "\n";
  }
}

void JumpFunctionAnalysis::createJumpFunction(CallInst *CI) {
  CallSite CS(CI);
  for (CallSite::arg_iterator AI = CS.arg_begin(), E = CS.arg_end();
       AI != E; ++AI) {
    Value *V = *AI;
    JumpFunction F;
    if (auto *CV = dyn_cast<Constant>(V))
      F.setConstant(CV);
    else
      F.setUnknown();
    JumpFunctionMap[CS].push_back(F);
  }
}

void JumpFunctionAnalysis::computeJumpFunctionForBasicBlock(BasicBlock &BB) {
  for (Instruction &I : BB) {
    auto *CI = dyn_cast<CallInst>(&I);
    if (!CI || CI->getNumOperands() == 0)
      continue;
    createJumpFunction(CI);
  }
}

void JumpFunctionAnalysis::analyzeFunction(Function &F) {
  auto DT = DominatorTree(F);
  for (auto DTN : depth_first(DT.getRootNode())) {
    BasicBlock *BB = DTN->getBlock();
    computeJumpFunctionForBasicBlock(*BB);
  }
}

void JumpFunctionAnalysis::computeJumpFunctions() {
  for (Function &F : M)
    if (!F.isDeclaration())
      analyzeFunction(F);
}

char JumpFunctionsPrinterLegacyPass::ID = 0;
INITIALIZE_PASS_BEGIN(JumpFunctionsPrinterLegacyPass, "print-jumpfunctions",
                      "Jump Functions printer", false, false)
INITIALIZE_PASS_DEPENDENCY(JumpFunctionsWrapperPass)
INITIALIZE_PASS_END(JumpFunctionsPrinterLegacyPass, "print-jumpfunctions",
                    "Jump Functions printer", false, false)

JumpFunctionsPrinterLegacyPass::JumpFunctionsPrinterLegacyPass()
    : ModulePass(ID) {
  initializeJumpFunctionsPrinterLegacyPassPass(
      *PassRegistry::getPassRegistry());
}

bool JumpFunctionsPrinterLegacyPass::runOnModule(Module &M) {
  auto &JumpFuncs = getAnalysis<JumpFunctionsWrapperPass>().getJumpFunctions();
  JumpFuncs.print(dbgs());
  return false;
}

void JumpFunctionsPrinterLegacyPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<JumpFunctionsWrapperPass>();
}

char JumpFunctionsWrapperPass::ID = 0;
INITIALIZE_PASS(JumpFunctionsWrapperPass, "jump-functions",
                "Compute Jump Functions for module", false, true)

JumpFunctionsWrapperPass::JumpFunctionsWrapperPass() : ModulePass(ID) {
  initializeJumpFunctionsWrapperPassPass(*PassRegistry::getPassRegistry());
}

bool JumpFunctionsWrapperPass::runOnModule(Module &M) {
  JumpFuncs.reset(new JumpFunctionAnalysis(M));
  return false;
}

void JumpFunctionsWrapperPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}
