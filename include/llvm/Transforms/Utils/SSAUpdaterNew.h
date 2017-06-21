//===-- SSAUpdaterNew.h - Unstructured SSA Update Tool -------------*- C++
//-*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file declares the SSAUpdaterNew class.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_SSAUPDATERNEW_H
#define LLVM_TRANSFORMS_UTILS_SSAUPDATERNEW_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include <string>

namespace llvm {

class BasicBlock;
class Instruction;
class LoadInst;
template <typename T> class ArrayRef;
template <typename T> class SmallVectorImpl;
class PHINode;
class Type;
class Use;
class Value;

/// \brief Helper class for SSA formation on a set of values defined in
/// multiple blocks.///
/// This is used when code duplication or another unstructured
/// transformation wants to rewrite a set of uses of one value with uses of a
/// set of values.
/// First, choose an unsigned int to represent your "variable".  As long as you
/// are consistent, it doesn not matter which you choose.
/// Set the name and type of the "variable" using setName and setType.
/// Now, for each definition of the "variable" that already exists or you've
/// inserted, call writeVariable(Var, BB, Value).
/// For each place you want to know the variable to use (for example, to replace
/// a use), call readVariableBeforeDef(Var, BB) or readVariableAfterDef(Var,
/// BB), it will place phi nodes if necessary.
/// If you have multiple definitions in the same block, call the read/write
/// routines in program order.
/// For example, if before i have:
/// if (foo)
///   a = b + c
/// d = b + c
/// and i place a new copy in the else block to do PRE:
/// if (foo)
/// ifbb:
///   a = b + c
/// else
/// elsebb:
///   temp = b + c
/// mergebb:
/// d = b + c
/// I would call:
/// setType(0, a->getType())
/// setName(0, "pretemp")
/// writeVariable(0, ifbb, a)
/// writeVariable(0, elsebb, temp)
/// and now to update d, i would call readVariableBeforeDef(0, mergebb), and it
/// will
/// create a phi node and return it to me.
/// if i have a loop with a use as so:
// pred:
// def (A)
// loop:
// use(A)
// def(A)
// branch to either pred, loop
// i would call writevariable(0, pred, A)
// then readvariablebeforedef(0, loop, A) to replace the use (because the use
// occurs
/// before the first definition)

class SSAUpdaterNew {

private:
  SmallVectorImpl<PHINode *> *InsertedPHIs;
  DenseMap<std::pair<unsigned, BasicBlock *>, Value *> CurrentDef;
  DenseSet<std::pair<unsigned, BasicBlock *>> VisitedBlocks;
  DenseMap<unsigned, Type *> CurrentType;
  DenseMap<unsigned, StringRef> CurrentName;

public:
  /// If InsertedPHIs is specified, it will be filled
  /// in with all PHI Nodes created by rewriting.
  explicit SSAUpdaterNew(SmallVectorImpl<PHINode *> *InsertedPHIs = nullptr);
  SSAUpdaterNew(const SSAUpdaterNew &) = delete;
  SSAUpdaterNew &operator=(const SSAUpdaterNew &) = delete;
  ~SSAUpdaterNew();

  // Mark a definition point of variable Var, occuring in BasicBlock BB, with
  // Value V.
  void writeVariable(unsigned Var, BasicBlock *BB, Value *V);
  // Get the definition of Var in BB, creating any phi nodes necessary to give a
  // singular answer.
  Value *readVariableAfterDef(unsigned Var, BasicBlock *);
  // Set the type to be used for variable Var
  void setType(unsigned Var, Type *Ty);
  void setName(unsigned Var, StringRef Name);
  Value *readVariableBeforeDef(unsigned Var, BasicBlock *);
  void minimizeInsertedPhis();

private:
  void minimizeInsertedPhisHelper(const SmallVectorImpl<PHINode *> &);
  void processSCC(const SmallPtrSetImpl<PHINode *> &);
  Value *addPhiOperands(unsigned Var, PHINode *);
  template <class RangeType>
  Value *tryRemoveTrivialPhi(unsigned Var, Instruction *Phi,
                             RangeType &Operands);
  Value *recursePhi(unsigned Var, Value *);
};
}

#endif // LLVM_TRANSFORMS_UTILS_SSAUPDATER_H
