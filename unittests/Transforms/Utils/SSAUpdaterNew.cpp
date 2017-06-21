//===- Local.cpp - Unit tests for Local -----------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/SSAUpdaterNew.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "gtest/gtest.h"

using namespace llvm;

TEST(SSAUpdaterNew, SimpleMerge) {
  SSAUpdaterNew Updater;
  LLVMContext C;
  Module M("SSAUpdaterTest", C);
  IRBuilder<> B(C);
  auto *F = Function::Create(
      FunctionType::get(B.getVoidTy(), {B.getInt32Ty(), B.getInt32Ty()}, false),
      GlobalValue::ExternalLinkage, "F", &M);

  // Make blocks
  BasicBlock *IfBB = BasicBlock::Create(C, "if", F);
  BasicBlock *TrueBB = BasicBlock::Create(C, "true", F);
  BasicBlock *FalseBB = BasicBlock::Create(C, "false", F);
  BasicBlock *MergeBB = BasicBlock::Create(C, "merge", F);
  B.SetInsertPoint(IfBB);
  B.CreateCondBr(B.getTrue(), TrueBB, FalseBB);
  B.SetInsertPoint(TrueBB);
  B.CreateBr(MergeBB);
  B.SetInsertPoint(FalseBB);
  B.CreateBr(MergeBB);
  Argument *FirstArg = &*F->arg_begin();
  Argument *SecondArg = &*(++(F->arg_begin()));
  B.SetInsertPoint(&TrueBB->front());
  Value *AddOp = B.CreateAdd(FirstArg, SecondArg);
  Updater.setType(0, B.getInt32Ty());
  Updater.setName(0, "update");
  Updater.writeVariable(0, TrueBB, AddOp);
  PHINode *FirstPhi =
      dyn_cast_or_null<PHINode>(Updater.readVariableBeforeDef(0, MergeBB));
  EXPECT_NE(FirstPhi, nullptr);
  EXPECT_TRUE(isa<UndefValue>(FirstPhi->getIncomingValueForBlock(FalseBB)));
  EXPECT_EQ(FirstPhi->getIncomingValueForBlock(TrueBB), AddOp);
  B.SetInsertPoint(FalseBB, FalseBB->begin());
  Value *AddOp2 = B.CreateAdd(FirstArg, SecondArg);
  Updater.writeVariable(0, FalseBB, AddOp2);
  PHINode *SecondPhi =
      dyn_cast_or_null<PHINode>(Updater.readVariableBeforeDef(0, MergeBB));
  EXPECT_NE(SecondPhi, nullptr);
  EXPECT_EQ(SecondPhi->getIncomingValueForBlock(TrueBB), AddOp);
  EXPECT_EQ(SecondPhi->getIncomingValueForBlock(FalseBB), AddOp2);
}
TEST(SSAUpdaterNew, Irreducible) {
  // Create the equivalent of
  // x = something
  // if (...)
  //    goto second_loop_entry
  // while (...) {
  // second_loop_entry:
  // }
  // use(x)
  SmallVector<PHINode *, 8> Inserted;
  SSAUpdaterNew Updater(&Inserted);
  LLVMContext C;
  Module M("SSAUpdaterTest", C);
  IRBuilder<> B(C);
  auto *F = Function::Create(
      FunctionType::get(B.getVoidTy(), {B.getInt32Ty(), B.getInt32Ty()}, false),
      GlobalValue::ExternalLinkage, "F", &M);

  // Make blocks
  BasicBlock *IfBB = BasicBlock::Create(C, "if", F);
  BasicBlock *LoopStartBB = BasicBlock::Create(C, "loopstart", F);
  BasicBlock *LoopMainBB = BasicBlock::Create(C, "loopmain", F);
  BasicBlock *AfterLoopBB = BasicBlock::Create(C, "afterloop", F);
  B.SetInsertPoint(IfBB);
  B.CreateCondBr(B.getTrue(), LoopMainBB, LoopStartBB);
  B.SetInsertPoint(LoopStartBB);
  B.CreateBr(LoopMainBB);
  B.SetInsertPoint(LoopMainBB);
  B.CreateCondBr(B.getTrue(), LoopStartBB, AfterLoopBB);
  Argument *FirstArg = &*F->arg_begin();
  Updater.setType(0, B.getInt32Ty());
  Updater.setName(0, "update");
  Updater.writeVariable(0, &F->getEntryBlock(), FirstArg);

  // The old updater crashes on an empty block, so add a return.
  B.SetInsertPoint(AfterLoopBB);
  ReturnInst *Return = B.CreateRet(FirstArg);
  // This will create two phis in a cycle, that are useless.
  Value *FirstResult = Updater.readVariableBeforeDef(0, AfterLoopBB);
  Return->setOperand(0, FirstResult);
  // Right now it is a phi.
  EXPECT_TRUE(isa<PHINode>(Return->getOperand(0)));
  EXPECT_EQ(Inserted.size(), 2u);
  Updater.minimizeInsertedPhis();
  // Now it should be an argument
  EXPECT_EQ(Return->getOperand(0), FirstArg);
  // And we should have no phis
  EXPECT_TRUE(Inserted.empty());
}
