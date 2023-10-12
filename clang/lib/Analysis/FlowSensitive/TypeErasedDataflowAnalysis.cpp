//===- TypeErasedDataflowAnalysis.cpp -------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file defines type-erased base types and functions for building dataflow
//  analyses that run over Control-Flow Graphs (CFGs).
//
//===----------------------------------------------------------------------===//

#include <algorithm>
#include <memory>
#include <optional>
#include <system_error>
#include <utility>
#include <vector>

#include "clang/AST/ASTDumper.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/OperationKinds.h"
#include "clang/AST/StmtCXX.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Analysis/Analyses/PostOrderCFGView.h"
#include "clang/Analysis/CFG.h"
#include "clang/Analysis/FlowSensitive/DataflowEnvironment.h"
#include "clang/Analysis/FlowSensitive/DataflowLattice.h"
#include "clang/Analysis/FlowSensitive/DataflowWorklist.h"
#include "clang/Analysis/FlowSensitive/RecordOps.h"
#include "clang/Analysis/FlowSensitive/StorageLocation.h"
#include "clang/Analysis/FlowSensitive/Transfer.h"
#include "clang/Analysis/FlowSensitive/TypeErasedDataflowAnalysis.h"
#include "clang/Analysis/FlowSensitive/Value.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Error.h"

#define DEBUG_TYPE "clang-dataflow"

namespace clang {
namespace dataflow {

/// Returns the index of `Block` in the successors of `Pred`.
static int blockIndexInPredecessor(const CFGBlock &Pred,
                                   const CFGBlock &Block) {
  auto BlockPos = llvm::find_if(
      Pred.succs(), [&Block](const CFGBlock::AdjacentBlock &Succ) {
        return Succ && Succ->getBlockID() == Block.getBlockID();
      });
  return BlockPos - Pred.succ_begin();
}

static bool isLoopHead(const CFGBlock &B) {
  if (const auto *T = B.getTerminatorStmt())
    switch (T->getStmtClass()) {
      case Stmt::WhileStmtClass:
      case Stmt::DoStmtClass:
      case Stmt::ForStmtClass:
      case Stmt::CXXForRangeStmtClass:
        return true;
      default:
        return false;
    }

  return false;
}

namespace {

#ifdef SAT_BOOL
// The return type of the visit functions in TerminatorVisitor. The first
// element represents the terminator expression (that is the conditional
// expression in case of a path split in the CFG). The second element
// represents whether the condition was true or false.
using TerminatorVisitorRetTy = std::pair<const Expr *, bool>;
#else
using BindingTy =
    std::optional<std::pair<const StorageLocation *, bool>>;

class NameVisitor
    : public ConstStmtVisitor<NameVisitor, BindingTy> {
public:
  NameVisitor(Environment &Env) : Env(Env) {}

  BindingTy VisitDeclRefExpr(const DeclRefExpr *S) {
    const ValueDecl *VD = S->getDecl();
    assert(VD != nullptr);

    // Some `DeclRefExpr`s aren't glvalues, so we can't associate them with a
    // `StorageLocation`, and there's also no sensible `Value` that we can
    // assign to them. Examples:
    // - Non-static member variables
    // - Non static member functions
    //   Note: Member operators are an exception to this, but apparently only
    //   if the `DeclRefExpr` is used within the callee of a
    //   `CXXOperatorCallExpr`. In other cases, for example when applying the
    //   address-of operator, the `DeclRefExpr` is a prvalue.
    if (!S->isGLValue())
      return std::nullopt;

    return std::make_pair(Env.getStorageLocation(*VD), true);
  }

  BindingTy VisitImplicitCastExpr(const ImplicitCastExpr *S) {
    const Expr *SubExpr = S->getSubExpr();
    assert(SubExpr != nullptr);

    switch (S->getCastKind()) {
    case CK_IntegralCast:
    case CK_LValueToRValue:
      return Visit(SubExpr);

    case CK_IntegralToBoolean:
    case CK_UncheckedDerivedToBase:
    case CK_ConstructorConversion:
    case CK_UserDefinedConversion:
    case CK_NoOp:
    case CK_NullToPointer:
    case CK_NullToMemberPointer:
    case CK_FunctionToPointerDecay:
    case CK_BuiltinFnToFnPtr:
      return std::nullopt;

    default:
      return std::nullopt;
    }
  }

  BindingTy VisitUnaryOperator(const UnaryOperator *S) {
    const Expr *SubExpr = S->getSubExpr();
    assert(SubExpr != nullptr);

    switch (S->getOpcode()) {
    // case UO_Deref: {
    //   const auto *SubExprVal =
    //       cast_or_null<PointerValue>(Env.getValue(*SubExpr));
    //   if (SubExprVal == nullptr)
    //     break;

    //   Env.setStorageLocation(*S, SubExprVal->getPointeeLoc());
    //   break;
    // }
    // case UO_AddrOf: {
    //   // FIXME: Model pointers to members.
    //   if (S->getType()->isMemberPointerType())
    //     break;

    //   if (StorageLocation *PointeeLoc = Env.getStorageLocation(*SubExpr))
    //     Env.setValue(*S, Env.create<PointerValue>(*PointeeLoc));
    //   break;
    // }
    case UO_LNot:
      if (auto SubExprBinding = Visit(SubExpr)) {
        SubExprBinding->second = !SubExprBinding->second;
        return SubExprBinding;
      }
      break;
    default:
      break;
    }
    return std::nullopt;
  }

  BindingTy VisitBinaryOperator(const BinaryOperator *S) {
    llvm::errs() << "Name: BinOp: ";
    const Expr *LHS = S->getLHS();
    assert(LHS != nullptr);

    const Expr *RHS = S->getRHS();
    assert(RHS != nullptr);

    switch (S->getOpcode()) {
    case BO_NE:
    case BO_EQ: {
      bool Negate = S->getOpcode() == BO_NE;
      if (Negate)
        llvm::errs() << "NE";
      else
        llvm::errs() << "EQ";

      if (auto LHSBinding = Visit(LHS)) {
        llvm::errs() << ": trying to bind LHS. RHS";
        // FIXME: handle case of obviously unreachable branch?
        auto *RHSVal = Env.getValue(*RHS);
        if (RHSVal == &Env.getBoolLiteralValue(Negate)) {
          llvm::errs() << " equals literal " << Negate << "\n";
          LHSBinding->second = !LHSBinding->second;
          return LHSBinding;
        }
        if (RHSVal == &Env.getBoolLiteralValue(!Negate)) {
          llvm::errs() << " equals literal " << !Negate << "\n";
          return LHSBinding;
        }
        llvm::errs() << "does not equal literal";
      }
      if (auto RHSBinding = Visit(RHS)) {
        llvm::errs() << ": trying to bind RHS. LHS";
        // FIXME: handle case of obviously unreachable branch?
        auto *LHSVal = Env.getValue(*LHS);
        if (LHSVal == &Env.getBoolLiteralValue(Negate)) {
          llvm::errs() << " equals literal " << Negate << "\n";
          RHSBinding->second = !RHSBinding->second;
          return RHSBinding;
        }
        if (LHSVal == &Env.getBoolLiteralValue(!Negate)) {
          llvm::errs() << " equals literal " << !Negate << "\n";
          return RHSBinding;
        }
        llvm::errs() << "does not equal literal.\n";
      }
      llvm::errs() << ". No bindings found.\n";
      break;
    }
    default:
      llvm::errs() << "Other\n";
      break;
    }
    return std::nullopt;
  }

  // void VisitMemberExpr(const MemberExpr *S) {
  //   ValueDecl *Member = S->getMemberDecl();
  //   assert(Member != nullptr);

  //   // FIXME: Consider assigning pointer values to function member expressions.
  //   if (Member->isFunctionOrFunctionTemplate())
  //     return;

  //   // FIXME: if/when we add support for modeling enums, use that support here.
  //   if (isa<EnumConstantDecl>(Member))
  //     return;

  //   if (auto *D = dyn_cast<VarDecl>(Member)) {
  //     if (D->hasGlobalStorage()) {
  //       auto *VarDeclLoc = Env.getStorageLocation(*D);
  //       if (VarDeclLoc == nullptr)
  //         return;

  //       Env.setStorageLocation(*S, *VarDeclLoc);
  //       return;
  //     }
  //   }

  //   RecordStorageLocation *BaseLoc = getBaseObjectLocation(*S, Env);
  //   if (BaseLoc == nullptr)
  //     return;

  //   auto *MemberLoc = BaseLoc->getChild(*Member);
  //   if (MemberLoc == nullptr)
  //     return;
  //   Env.setStorageLocation(*S, *MemberLoc);
  // }

  // void VisitConditionalOperator(const ConditionalOperator *S) {
  //   /*SIMPLE*/ // revisit the comment
  //   // FIXME: Revisit this once flow conditions are added to the framework. For
  //   // `a = b ? c : d` we can add `b => a == c && !b => a == d` to the flow
  //   // condition.
  //   if (S->isGLValue())
  //     Env.setStorageLocation(*S, Env.createObject(S->getType()));
  //   else if (Value *Val = Env.createValue(S->getType()))
  //     Env.setValue(*S, *Val);
  // }

  BindingTy VisitParenExpr(const ParenExpr *S) {
    // The CFG does not contain `ParenExpr` as top-level statements in basic
    // blocks, however manual traversal to sub-expressions may encounter them.
    // Redirect to the sub-expression.
    auto *SubExpr = S->getSubExpr();
    assert(SubExpr != nullptr);
    return Visit(SubExpr);
  }

 private:
  Environment &Env;
};

// For a condition expression, its location and the bool to which it is bound.
// struct CondBinding {
//   const StorageLocation *Loc;
//   bool Val;
// };
using TerminatorVisitorRetTy =
    std::optional<std::pair<const Expr *, BindingTy>>;
#endif

/// Extends the flow condition of an environment based on a terminator
/// statement.
class TerminatorVisitor
    : public ConstStmtVisitor<TerminatorVisitor, TerminatorVisitorRetTy> {
public:
#ifdef SAT_BOOL
  TerminatorVisitor(const StmtToEnvMap &StmtToEnv, Environment &Env,
                    int BlockSuccIdx)
      : StmtToEnv(StmtToEnv), Env(Env), BlockSuccIdx(BlockSuccIdx) {}
#else
  TerminatorVisitor(Environment &Env, int BlockSuccIdx)
      : Env(Env), BlockSuccIdx(BlockSuccIdx) {}
#endif

  TerminatorVisitorRetTy VisitIfStmt(const IfStmt *S) {
    auto *Cond = S->getCond();
    assert(Cond != nullptr);
    return extendFlowCondition(*Cond);
  }

  TerminatorVisitorRetTy VisitWhileStmt(const WhileStmt *S) {
    auto *Cond = S->getCond();
    assert(Cond != nullptr);
    return extendFlowCondition(*Cond);
  }

  TerminatorVisitorRetTy VisitDoStmt(const DoStmt *S) {
    auto *Cond = S->getCond();
    assert(Cond != nullptr);
    return extendFlowCondition(*Cond);
  }

  TerminatorVisitorRetTy VisitForStmt(const ForStmt *S) {
    auto *Cond = S->getCond();
    if (Cond != nullptr)
      return extendFlowCondition(*Cond);
#ifdef SAT_BOOL
    return {nullptr, false};
#else
    return std::nullopt;
#endif
  }

  TerminatorVisitorRetTy VisitCXXForRangeStmt(const CXXForRangeStmt *) {
    // Don't do anything special for CXXForRangeStmt, because the condition
    // (being implicitly generated) isn't visible from the loop body.
#ifdef SAT_BOOL
    return {nullptr, false};
#else
    return std::nullopt;
#endif
  }

  TerminatorVisitorRetTy VisitBinaryOperator(const BinaryOperator *S) {
    assert(S->getOpcode() == BO_LAnd || S->getOpcode() == BO_LOr);
    auto *LHS = S->getLHS();
    assert(LHS != nullptr);
    return extendFlowCondition(*LHS);
  }

  TerminatorVisitorRetTy
  VisitConditionalOperator(const ConditionalOperator *S) {
    auto *Cond = S->getCond();
    assert(Cond != nullptr);
    return extendFlowCondition(*Cond);
  }

private:
  // Instead, update the map.
#ifdef SAT_BOOL
  TerminatorVisitorRetTy extendFlowCondition(const Expr &Cond) {
    // The terminator sub-expression might not be evaluated.
    if (Env.getValue(Cond) == nullptr)
      transfer(StmtToEnv, Cond, Env);

    auto *Val = cast_or_null<BoolValue>(Env.getValue(Cond));
    // Value merging depends on flow conditions from different environments
    // being mutually exclusive -- that is, they cannot both be true in their
    // entirety (even if they may share some clauses). So, we need *some* value
    // for the condition expression, even if just an atom.
    if (Val == nullptr) {
      Val = &Env.makeAtomicBoolValue();
      Env.setValue(Cond, *Val);
    }

    bool ConditionValue = true;
    // The condition must be inverted for the successor that encompasses the
    // "else" branch, if such exists.
    if (BlockSuccIdx == 1) {
      Val = &Env.makeNot(*Val);
      ConditionValue = false;
    }
    Env.addToFlowCondition(Val->formula());
    return {&Cond, ConditionValue};
  }
#else
  TerminatorVisitorRetTy extendFlowCondition(const Expr &Cond) {
    auto Binding = NameVisitor(Env).Visit(&Cond);
    if (Binding && BlockSuccIdx == 1)
      Binding->second = !Binding->second;
    return std::make_pair(&Cond, Binding);
  }
#endif

#ifdef SAT_BOOL
  const StmtToEnvMap &StmtToEnv;
#endif
  Environment &Env;
  int BlockSuccIdx;
};

/// Holds data structures required for running dataflow analysis.
struct AnalysisContext {
  AnalysisContext(const ControlFlowContext &CFCtx,
                  TypeErasedDataflowAnalysis &Analysis,
                  const Environment &InitEnv,
                  llvm::ArrayRef<std::optional<TypeErasedDataflowAnalysisState>>
                      BlockStates)
      : CFCtx(CFCtx), Analysis(Analysis), InitEnv(InitEnv),
        Log(*InitEnv.getDataflowAnalysisContext().getOptions().Log),
        BlockStates(BlockStates) {
    Log.beginAnalysis(CFCtx, Analysis);
  }
  ~AnalysisContext() { Log.endAnalysis(); }

  /// Contains the CFG being analyzed.
  const ControlFlowContext &CFCtx;
  /// The analysis to be run.
  TypeErasedDataflowAnalysis &Analysis;
  /// Initial state to start the analysis.
  const Environment &InitEnv;
  Logger &Log;
  /// Stores the state of a CFG block if it has been evaluated by the analysis.
  /// The indices correspond to the block IDs.
  llvm::ArrayRef<std::optional<TypeErasedDataflowAnalysisState>> BlockStates;
};

class PrettyStackTraceAnalysis : public llvm::PrettyStackTraceEntry {
public:
  PrettyStackTraceAnalysis(const ControlFlowContext &CFCtx, const char *Message)
      : CFCtx(CFCtx), Message(Message) {}

  void print(raw_ostream &OS) const override {
    OS << Message << "\n";
    OS << "Decl:\n";
    CFCtx.getDecl().dump(OS);
    OS << "CFG:\n";
    CFCtx.getCFG().print(OS, LangOptions(), false);
  }

private:
  const ControlFlowContext &CFCtx;
  const char *Message;
};

class PrettyStackTraceCFGElement : public llvm::PrettyStackTraceEntry {
public:
  PrettyStackTraceCFGElement(const CFGElement &Element, int BlockIdx,
                             int ElementIdx, const char *Message)
      : Element(Element), BlockIdx(BlockIdx), ElementIdx(ElementIdx),
        Message(Message) {}

  void print(raw_ostream &OS) const override {
    OS << Message << ": Element [B" << BlockIdx << "." << ElementIdx << "]\n";
    if (auto Stmt = Element.getAs<CFGStmt>()) {
      OS << "Stmt:\n";
      ASTDumper Dumper(OS, false);
      Dumper.Visit(Stmt->getStmt());
    }
  }

private:
  const CFGElement &Element;
  int BlockIdx;
  int ElementIdx;
  const char *Message;
};

// Builds a joined TypeErasedDataflowAnalysisState from 0 or more sources,
// each of which may be owned (built as part of the join) or external (a
// reference to an Environment that will outlive the builder).
// Avoids unneccesary copies of the environment.
class JoinedStateBuilder {
  AnalysisContext &AC;
  std::vector<const TypeErasedDataflowAnalysisState *> All;
  std::deque<TypeErasedDataflowAnalysisState> Owned;

  TypeErasedDataflowAnalysisState
  join(const TypeErasedDataflowAnalysisState &L,
       const TypeErasedDataflowAnalysisState &R) {
    return {AC.Analysis.joinTypeErased(L.Lattice, R.Lattice),
            Environment::join(L.Env, R.Env, AC.Analysis)};
  }

public:
  JoinedStateBuilder(AnalysisContext &AC) : AC(AC) {}

  void addOwned(TypeErasedDataflowAnalysisState State) {
    Owned.push_back(std::move(State));
    All.push_back(&Owned.back());
  }
  void addUnowned(const TypeErasedDataflowAnalysisState &State) {
    All.push_back(&State);
  }
  TypeErasedDataflowAnalysisState take() && {
    if (All.empty())
      // FIXME: Consider passing `Block` to Analysis.typeErasedInitialElement
      // to enable building analyses like computation of dominators that
      // initialize the state of each basic block differently.
      return {AC.Analysis.typeErasedInitialElement(), AC.InitEnv.fork()};
    if (All.size() == 1)
      return Owned.empty() ? All.front()->fork() : std::move(Owned.front());

    auto Result = join(*All[0], *All[1]);
    for (unsigned I = 2; I < All.size(); ++I)
      Result = join(Result, *All[I]);
    return Result;
  }
};

} // namespace

/// Computes the input state for a given basic block by joining the output
/// states of its predecessors.
///
/// Requirements:
///
///   All predecessors of `Block` except those with loop back edges must have
///   already been transferred. States in `AC.BlockStates` that are set to
///   `std::nullopt` represent basic blocks that are not evaluated yet.
static TypeErasedDataflowAnalysisState
computeBlockInputState(const CFGBlock &Block, AnalysisContext &AC) {
  std::vector<const CFGBlock *> Preds(Block.pred_begin(), Block.pred_end());
  if (Block.getTerminator().isTemporaryDtorsBranch()) {
    // This handles a special case where the code that produced the CFG includes
    // a conditional operator with a branch that constructs a temporary and
    // calls a destructor annotated as noreturn. The CFG models this as follows:
    //
    // B1 (contains the condition of the conditional operator) - succs: B2, B3
    // B2 (contains code that does not call a noreturn destructor) - succs: B4
    // B3 (contains code that calls a noreturn destructor) - succs: B4
    // B4 (has temporary destructor terminator) - succs: B5, B6
    // B5 (noreturn block that is associated with the noreturn destructor call)
    // B6 (contains code that follows the conditional operator statement)
    //
    // The first successor (B5 above) of a basic block with a temporary
    // destructor terminator (B4 above) is the block that evaluates the
    // destructor. If that block has a noreturn element then the predecessor
    // block that constructed the temporary object (B3 above) is effectively a
    // noreturn block and its state should not be used as input for the state
    // of the block that has a temporary destructor terminator (B4 above). This
    // holds regardless of which branch of the ternary operator calls the
    // noreturn destructor. However, it doesn't cases where a nested ternary
    // operator includes a branch that contains a noreturn destructor call.
    //
    // See `NoreturnDestructorTest` for concrete examples.
    if (Block.succ_begin()->getReachableBlock() != nullptr &&
        Block.succ_begin()->getReachableBlock()->hasNoReturnElement()) {
      auto &StmtToBlock = AC.CFCtx.getStmtToBlock();
      auto StmtBlock = StmtToBlock.find(Block.getTerminatorStmt());
      assert(StmtBlock != StmtToBlock.end());
      llvm::erase_value(Preds, StmtBlock->getSecond());
    }
  }

  JoinedStateBuilder Builder(AC);
  for (const CFGBlock *Pred : Preds) {
    // Skip if the `Block` is unreachable or control flow cannot get past it.
    if (!Pred || Pred->hasNoReturnElement())
      continue;

    // Skip if `Pred` was not evaluated yet. This could happen if `Pred` has a
    // loop back edge to `Block`.
    const std::optional<TypeErasedDataflowAnalysisState> &MaybePredState =
        AC.BlockStates[Pred->getBlockID()];
    if (!MaybePredState)
      continue;

    if (AC.Analysis.builtinOptions()) {
      if (const Stmt *PredTerminatorStmt = Pred->getTerminatorStmt()) {
        // We have a terminator: we need to mutate an environment to describe
        // when the terminator is taken. Copy now.
        TypeErasedDataflowAnalysisState Copy = MaybePredState->fork();

        const StmtToEnvMap StmtToEnv(AC.CFCtx, AC.BlockStates);
#ifdef SAT_BOOL
        auto [Cond, CondValue] =
            TerminatorVisitor(StmtToEnv, Copy.Env,
                              blockIndexInPredecessor(*Pred, Block))
                .Visit(PredTerminatorStmt);
        if (Cond != nullptr)
          // FIXME: Call transferBranchTypeErased even if BuiltinTransferOpts
          // are not set.
          AC.Analysis.transferBranchTypeErased(CondValue, Cond, Copy.Lattice,
                                               Copy.Env);
#else
        int index = blockIndexInPredecessor(*Pred, Block);
        if (auto Mapping =
                TerminatorVisitor(Copy.Env, index).Visit(PredTerminatorStmt)) {
          auto [Cond, Binding] = *Mapping;
          if (Binding) {
            auto [Loc, Val] = *Binding;
            Copy.Env.setValue(*Loc, Copy.Env.getBoolLiteralValue(Val));
          }
          // FIXME: Call transferBranchTypeErased even if BuiltinTransferOpts
          // are not set.
          AC.Analysis.transferBranchTypeErased((index == 0), Cond, Copy.Lattice,
                                               Copy.Env);
        }
#endif
        Builder.addOwned(std::move(Copy));
        continue;
      }
    }
    Builder.addUnowned(*MaybePredState);
  }
  return std::move(Builder).take();
}

/// Built-in transfer function for `CFGStmt`.
static void
builtinTransferStatement(const CFGStmt &Elt,
                         TypeErasedDataflowAnalysisState &InputState,
                         AnalysisContext &AC) {
  const Stmt *S = Elt.getStmt();
  assert(S != nullptr);
  transfer(StmtToEnvMap(AC.CFCtx, AC.BlockStates), *S, InputState.Env);
}

/// Built-in transfer function for `CFGInitializer`.
static void
builtinTransferInitializer(const CFGInitializer &Elt,
                           TypeErasedDataflowAnalysisState &InputState) {
  const CXXCtorInitializer *Init = Elt.getInitializer();
  assert(Init != nullptr);

  auto &Env = InputState.Env;
  auto &ThisLoc = *Env.getThisPointeeStorageLocation();

  if (!Init->isAnyMemberInitializer())
    // FIXME: Handle base initialization
    return;

  auto *InitExpr = Init->getInit();
  assert(InitExpr != nullptr);

  const FieldDecl *Member = nullptr;
  RecordStorageLocation *ParentLoc = &ThisLoc;
  StorageLocation *MemberLoc = nullptr;
  if (Init->isMemberInitializer()) {
    Member = Init->getMember();
    MemberLoc = ThisLoc.getChild(*Member);
  } else {
    IndirectFieldDecl *IndirectField = Init->getIndirectMember();
    assert(IndirectField != nullptr);
    MemberLoc = &ThisLoc;
    for (const auto *I : IndirectField->chain()) {
      Member = cast<FieldDecl>(I);
      ParentLoc = cast<RecordStorageLocation>(MemberLoc);
      MemberLoc = ParentLoc->getChild(*Member);
    }
  }
  assert(Member != nullptr);
  assert(MemberLoc != nullptr);

  // FIXME: Instead of these case distinctions, we would ideally want to be able
  // to simply use `Environment::createObject()` here, the same way that we do
  // this in `TransferVisitor::VisitInitListExpr()`. However, this would require
  // us to be able to build a list of fields that we then use to initialize an
  // `RecordStorageLocation` -- and the problem is that, when we get here,
  // the `RecordStorageLocation` already exists. We should explore if there's
  // anything that we can do to change this.
  if (Member->getType()->isReferenceType()) {
    auto *InitExprLoc = Env.getStorageLocation(*InitExpr);
    if (InitExprLoc == nullptr)
      return;

    ParentLoc->setChild(*Member, InitExprLoc);
  } else if (auto *InitExprVal = Env.getValue(*InitExpr)) {
    if (Member->getType()->isRecordType()) {
      auto *InitValStruct = cast<RecordValue>(InitExprVal);
      // FIXME: Rather than performing a copy here, we should really be
      // initializing the field in place. This would require us to propagate the
      // storage location of the field to the AST node that creates the
      // `RecordValue`.
      copyRecord(InitValStruct->getLoc(),
                 *cast<RecordStorageLocation>(MemberLoc), Env);
    } else {
      Env.setValue(*MemberLoc, *InitExprVal);
    }
  }
}

static void builtinTransfer(const CFGElement &Elt,
                            TypeErasedDataflowAnalysisState &State,
                            AnalysisContext &AC) {
  switch (Elt.getKind()) {
  case CFGElement::Statement:
    builtinTransferStatement(Elt.castAs<CFGStmt>(), State, AC);
    break;
  case CFGElement::Initializer:
    builtinTransferInitializer(Elt.castAs<CFGInitializer>(), State);
    break;
  case CFGElement::LifetimeEnds:
    // Removing declarations when their lifetime ends serves two purposes:
    // - Eliminate unnecessary clutter from `Environment::DeclToLoc`
    // - Allow us to assert that, when joining two `Environment`s, the two
    //   `DeclToLoc` maps never contain entries that map the same declaration to
    //   different storage locations.
    if (const ValueDecl *VD = Elt.castAs<CFGLifetimeEnds>().getVarDecl())
      State.Env.removeDecl(*VD);
    break;
  default:
    // FIXME: Evaluate other kinds of `CFGElement`
    break;
  }
}

/// Transfers `State` by evaluating each element in the `Block` based on the
/// `AC.Analysis` specified.
///
/// Built-in transfer functions (if the option for `ApplyBuiltinTransfer` is set
/// by the analysis) will be applied to the element before evaluation by the
/// user-specified analysis.
/// `PostVisitCFG` (if provided) will be applied to the element after evaluation
/// by the user-specified analysis.
static TypeErasedDataflowAnalysisState
transferCFGBlock(const CFGBlock &Block, AnalysisContext &AC,
                 std::function<void(const CFGElement &,
                                    const TypeErasedDataflowAnalysisState &)>
                     PostVisitCFG = nullptr) {
  AC.Log.enterBlock(Block, PostVisitCFG != nullptr);
  auto State = computeBlockInputState(Block, AC);
  AC.Log.recordState(State);
  int ElementIdx = 1;
  for (const auto &Element : Block) {
    PrettyStackTraceCFGElement CrashInfo(Element, Block.getBlockID(),
                                         ElementIdx++, "transferCFGBlock");

    AC.Log.enterElement(Element);
    // Built-in analysis
    if (AC.Analysis.builtinOptions()) {
      builtinTransfer(Element, State, AC);
    }

    // User-provided analysis
    AC.Analysis.transferTypeErased(Element, State.Lattice, State.Env);

    // Post processing
    if (PostVisitCFG) {
      PostVisitCFG(Element, State);
    }
    AC.Log.recordState(State);
  }
  return State;
}

llvm::Expected<std::vector<std::optional<TypeErasedDataflowAnalysisState>>>
runTypeErasedDataflowAnalysis(
    const ControlFlowContext &CFCtx, TypeErasedDataflowAnalysis &Analysis,
    const Environment &InitEnv,
    std::function<void(const CFGElement &,
                       const TypeErasedDataflowAnalysisState &)>
        PostVisitCFG) {
  PrettyStackTraceAnalysis CrashInfo(CFCtx, "runTypeErasedDataflowAnalysis");

  PostOrderCFGView POV(&CFCtx.getCFG());
  ForwardDataflowWorklist Worklist(CFCtx.getCFG(), &POV);

  std::vector<std::optional<TypeErasedDataflowAnalysisState>> BlockStates(
      CFCtx.getCFG().size());

  // The entry basic block doesn't contain statements so it can be skipped.
  const CFGBlock &Entry = CFCtx.getCFG().getEntry();
  BlockStates[Entry.getBlockID()] = {Analysis.typeErasedInitialElement(),
                                     InitEnv.fork()};
  Worklist.enqueueSuccessors(&Entry);

  AnalysisContext AC(CFCtx, Analysis, InitEnv, BlockStates);

  // Bugs in lattices and transfer functions can prevent the analysis from
  // converging. To limit the damage (infinite loops) that these bugs can cause,
  // limit the number of iterations.
  // FIXME: Consider making the maximum number of iterations configurable.
  // FIXME: Consider restricting the number of backedges followed, rather than
  // iterations.
  // FIXME: Set up statistics (see llvm/ADT/Statistic.h) to count average number
  // of iterations, number of functions that time out, etc.
  static constexpr uint32_t MaxAverageVisitsPerBlock = 4;
  static constexpr uint32_t AbsoluteMaxIterations = 1 << 16;
  const uint32_t RelativeMaxIterations =
      MaxAverageVisitsPerBlock * BlockStates.size();
  const uint32_t MaxIterations =
      std::min(RelativeMaxIterations, AbsoluteMaxIterations);
  uint32_t Iterations = 0;
  while (const CFGBlock *Block = Worklist.dequeue()) {
    LLVM_DEBUG(llvm::dbgs()
               << "Processing Block " << Block->getBlockID() << "\n");
    if (++Iterations > MaxIterations) {
      return llvm::createStringError(std::errc::timed_out,
                                     "maximum number of iterations reached");
    }

    const std::optional<TypeErasedDataflowAnalysisState> &OldBlockState =
        BlockStates[Block->getBlockID()];
    TypeErasedDataflowAnalysisState NewBlockState =
        transferCFGBlock(*Block, AC);
    LLVM_DEBUG({
      llvm::errs() << "New Env:\n";
      NewBlockState.Env.dump();
    });

    if (OldBlockState) {
      LLVM_DEBUG({
        llvm::errs() << "Old Env:\n";
        OldBlockState->Env.dump();
      });
      if (isLoopHead(*Block)) {
        LatticeJoinEffect Effect1 = Analysis.widenTypeErased(
            NewBlockState.Lattice, OldBlockState->Lattice);
        LatticeJoinEffect Effect2 =
            NewBlockState.Env.widen(OldBlockState->Env, Analysis);
        if (Effect1 == LatticeJoinEffect::Unchanged &&
            Effect2 == LatticeJoinEffect::Unchanged) {
          // The state of `Block` didn't change from widening so there's no need
          // to revisit its successors.
          AC.Log.blockConverged();
          continue;
        }
      } else if (Analysis.isEqualTypeErased(OldBlockState->Lattice,
                                            NewBlockState.Lattice) &&
                 OldBlockState->Env.equivalentTo(NewBlockState.Env, Analysis)) {
        // The state of `Block` didn't change after transfer so there's no need
        // to revisit its successors.
        AC.Log.blockConverged();
        continue;
      }
    }

    BlockStates[Block->getBlockID()] = std::move(NewBlockState);

    // Do not add unreachable successor blocks to `Worklist`.
    if (Block->hasNoReturnElement())
      continue;

    Worklist.enqueueSuccessors(Block);
  }
  // FIXME: Consider evaluating unreachable basic blocks (those that have a
  // state set to `std::nullopt` at this point) to also analyze dead code.

  if (PostVisitCFG) {
    for (const CFGBlock *Block : CFCtx.getCFG()) {
      // Skip blocks that were not evaluated.
      if (!BlockStates[Block->getBlockID()])
        continue;
      transferCFGBlock(*Block, AC, PostVisitCFG);
    }
  }

  return std::move(BlockStates);
}

} // namespace dataflow
} // namespace clang
