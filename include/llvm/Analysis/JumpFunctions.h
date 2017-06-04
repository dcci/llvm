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

#include "llvm/Pass.h"

using namespace llvm;

class JumpFunctionsWrapperPass : public ModulePass {
public:
  JumpFunctionsWrapperPass();
  static char ID;

  bool runOnModule(Module &) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override;

private:
#if 0
  std::unique_ptr<JumpFunctions> JF;
#endif
};

#endif // LLVM_ANALYSIS_JUMPFUNCTIONS_H
