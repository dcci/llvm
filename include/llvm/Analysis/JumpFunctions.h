//===- JumpFunctions.h - Compute Jump Functions  -------------------------===//
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

#ifndef LLVM_ANALYSIS_JUMPFUNCTIONS_H
#define LLVM_ANALYSIS_JUMPFUNCTIONS_H

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"

using namespace llvm;

struct JumpFunction {
  enum FType {
    Unknown,
    Constant
  };
  enum FType Type;

  // If FType is constant, this field contains the constant value hold.
  Value *ConstVal;
};

class JumpFunctionAnalysis {
public:
  JumpFunctionAnalysis(Module &M, CallGraph &CG);
  void computeJumpFunctions();
  void analyzeFunction(Function &);
  void analyzeParamsInBasicBlock(BasicBlock &);
  void computeJumpFunctionForBasicBlock(BasicBlock &);
  void createJumpFunction(CallSite *, Value *, unsigned);

private:
  Module &M;
  CallGraph &CG;
};

class JumpFunctionsWrapperPass : public ModulePass {
public:
  JumpFunctionsWrapperPass();
  static char ID;

  bool runOnModule(Module &) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;

private:
  std::unique_ptr<JumpFunctionAnalysis> JumpFuncs;
};

#endif // LLVM_ANALYSIS_JUMPFUNCTIONS_H
