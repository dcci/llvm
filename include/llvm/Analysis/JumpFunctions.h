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

class JumpFunction {
public:
  void setConstant(Constant *C) {
    Type = Constant;
    ConstVal = C;
  }

  void setUnknown() {
    Type = Unknown;
    ConstVal = nullptr;
  }

  bool isConstant() { return Type == Constant; }
  bool isUnknown() { return Type == Unknown; }

  Value *getConstant() {
    assert(Type == Constant && "This jump function is not constant!");
    return ConstVal;
  }

private:
  enum FType {
    Unknown,
    Constant
  };
  enum FType Type;

  // If FType is constant, this field contains the constant value hold.
  Value *ConstVal = nullptr;
};

class JumpFunctionAnalysis {
public:
  JumpFunctionAnalysis(Module &M);
  void computeJumpFunctions();
  void analyzeFunction(Function &);
  void computeJumpFunctionForBasicBlock(BasicBlock &);
  void createJumpFunction(CallInst *);
  void print(raw_ostream &OS) const;

  std::vector<JumpFunction> getJumpFunctionForCallSite(CallSite &CS) {
    return JumpFunctionMap[CS];
  }

private:
  Module &M;
  DenseMap<CallSite, std::vector<JumpFunction>> JumpFunctionMap;
};

class JumpFunctionsPrinterLegacyPass : public ModulePass {
public:
  JumpFunctionsPrinterLegacyPass();
  static char ID;

  bool runOnModule(Module &) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;
};

class JumpFunctionsWrapperPass : public ModulePass {
public:
  JumpFunctionsWrapperPass();
  static char ID;

  bool runOnModule(Module &) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;

  JumpFunctionAnalysis &getJumpFunctions() { return *JumpFuncs; }
  const JumpFunctionAnalysis &getJumpFunctions() const { return *JumpFuncs; }

private:
  std::unique_ptr<JumpFunctionAnalysis> JumpFuncs;
};

#endif // LLVM_ANALYSIS_JUMPFUNCTIONS_H
