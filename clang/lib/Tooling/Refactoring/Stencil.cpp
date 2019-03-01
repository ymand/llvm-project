//===--- Stencil.cpp - Stencil implementation -------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/Stencil.h"

#include <atomic>
#include <string>

#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTTypeTraits.h"
#include "clang/AST/Expr.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/FixIt.h"
#include "llvm/Support/Errc.h"

namespace clang {
namespace tooling {

// A down_cast function to safely down cast a StencilPartInterface to a subclass
// D. Returns nullptr if P is not an instance of D.
template <typename D> const D *down_cast(const StencilPartInterface *P) {
  if (P == nullptr || D::typeId() != P->typeId())
    return nullptr;
  return static_cast<const D *>(P);
}

// For guaranteeing unique ids on NodeId creation.
static size_t nextId() {
  // Start with a relatively high number to avoid bugs if the user mixes
  // explicitly-numbered ids with those generated with `NextId()`. Similarly, we
  // choose a number that allows generated ids to be easily recognized.
  static std::atomic<size_t> Next(2222);
  return Next.fetch_add(1, std::memory_order_relaxed);
}

// Gets the source text of the arguments to the call expression. Includes all
// source between the parentheses delimiting the call.
static StringRef
getArgumentsText(const CallExpr &CE,
                 const ast_matchers::MatchFinder::MatchResult &Result) {
  auto &SM = *Result.SourceManager;
  auto &LangOpts = Result.Context->getLangOpts();
  auto Range = CharSourceRange::getCharRange(
      fixit::findOpenParen(CE, SM, LangOpts).getLocWithOffset(1),
      CE.getRParenLoc());
  return Lexer::getSourceText(Range, SM, LangOpts);
}

// Gets the source text of the statements in the compound statement. Includes
// all source between the braces.
static StringRef
getStatementsText(const CompoundStmt &CS,
                  const ast_matchers::MatchFinder::MatchResult &Result) {
  auto Range = CharSourceRange::getCharRange(
      CS.getLBracLoc().getLocWithOffset(1), CS.getRBracLoc());
  return Lexer::getSourceText(Range, *Result.SourceManager,
                              Result.Context->getLangOpts());
}

static llvm::Expected<ast_type_traits::DynTypedNode>
getNode(const ast_matchers::BoundNodes &Nodes, StringRef Id) {
  auto &NodesMap = Nodes.getMap();
  auto It = NodesMap.find(Id);
  if (It == NodesMap.end()) {
    return llvm::make_error<llvm::StringError>(llvm::errc::invalid_argument,
                                               "Id not bound: " + Id);
  }
  return It->second;
}

namespace {
using ::clang::ast_matchers::MatchFinder;
using ::llvm::errc;
using ::llvm::Error;
using ::llvm::Expected;
using ::llvm::StringError;

// An arbitrary fragment of code within a stencil.
struct RawTextData {
  explicit RawTextData(std::string T) : Text(std::move(T)) {}
  std::string Text;
};

bool operator==(const RawTextData &A, const RawTextData &B) {
  return A.Text == B.Text;
}

// A debugging operation to dump the AST for a particular (bound) AST node.
struct DebugPrintNodeOpData {
  explicit DebugPrintNodeOpData(std::string S) : Id(std::move(S)) {}
  std::string Id;
};

bool operator==(const DebugPrintNodeOpData &A, const DebugPrintNodeOpData &B) {
  return A.Id == B.Id;
}

// A reference to a particular (bound) AST node.
struct NodeRefData {
  explicit NodeRefData(std::string S) : Id(std::move(S)) {}
  std::string Id;
};

bool operator==(const NodeRefData &A, const NodeRefData &B) {
  return A.Id == B.Id;
}

// A stencil operation that, given a reference to an expression e and a Part
// describing a member m, yields "e->m", when e is a pointer, "e2->m" when e =
// "*e2" and "e.m" otherwise.
struct MemberOpData  {
  MemberOpData(StringRef ObjectId, StencilPart Member)
      : ObjectId(ObjectId), Member(std::move(Member)) {}
  std::string ObjectId;
  StencilPart Member;
};

bool operator==(const MemberOpData &A, const MemberOpData &B) {
  return A.ObjectId == B.ObjectId && A.Member == B.Member;
}

// Operations all take a single reference to a Expr parameter, e.
struct ExprOpData {
  enum class Operator {
    // Yields "e2" when e = "&e2" (with '&' the builtin operator), "*e" when e
    // is a pointer and "e" otherwise.
    kValue,
    // Yields "e2" when e = "*e2" (with '*' the builtin operator), "e" when e is
    // a pointer and "&e" otherwise.
    kAddress,
    // Wraps e in parens if it may parse differently depending on context. For
    // example, a binary operation is always wrapped while a variable reference
    // is never wrapped.
    kParens,
  };

  ExprOpData(Operator Op, StringRef Id) : Op(Op), Id(Id) {}

  Operator Op;
  std::string Id;
};

bool operator==(const ExprOpData &A, const ExprOpData &B) {
  return A.Op == B.Op && A.Id == B.Id;
}

// Given a reference to a named declaration d (NamedDecl), yields
// the name. "d" must have an identifier name (that is, constructors are
// not valid arguments to the Name operation).
struct NameOpData {
  explicit NameOpData(StringRef Id)
      : Id(Id) {}
  std::string Id;
};

bool operator==(const NameOpData &A, const NameOpData &B) {
  return A.Id == B.Id;
}

// Given a reference to a call expression (CallExpr), yields the
// arguments as a comma separated list.
struct ArgsOpData {
  explicit ArgsOpData(StringRef Id) : Id(Id) {}
  std::string Id;
};

bool operator==(const ArgsOpData &A, const ArgsOpData &B) {
  return A.Id == B.Id;
}

// Given a reference to a statement, yields the contents between the braces,
// if it is compound, or the statement and its trailing semicolon (if any)
// otherwise.
struct StatementsOpData {
  explicit StatementsOpData(StringRef Id) : Id(Id) {}
  std::string Id;
};

bool operator==(const StatementsOpData &A, const StatementsOpData &B) {
  return A.Id == B.Id;
}

// Given a function and a reference to a node, yields the string that results
// from applying the function to the referenced node.
struct NodeFunctionOpData {
  NodeFunctionOpData(stencil_generators::NodeFunction F, StringRef Id)
      : F(std::move(F)), Id(Id) {}
  stencil_generators::NodeFunction F;
  std::string Id;
};

bool operator==(const NodeFunctionOpData &A, const NodeFunctionOpData &B) {
  return false;
}

// Given a function and a stencil part, yields the string that results from
// applying the function to the part's evaluation.
struct StringFunctionOpData {
  StringFunctionOpData(stencil_generators::StringFunction F, StencilPart Part)
      :        F(std::move(F)),
        Part(std::move(Part)) {}
  stencil_generators::StringFunction F;
  StencilPart Part;
};

bool operator==(const StringFunctionOpData &A, const StringFunctionOpData &B) {
  return false;
}

Error evalData(const RawTextData &Data, const MatchFinder::MatchResult &,
           std::string *Result) {
  Result->append(Data.Text);
  return Error::success();
}

Error evalData(const DebugPrintNodeOpData &Data,
           const MatchFinder::MatchResult &Match, std::string *Result) {
  std::string Output;
  llvm::raw_string_ostream Os(Output);
  auto NodeOrErr = getNode(Match.Nodes, Data.Id);
  if (auto Err = NodeOrErr.takeError()) {
    return Err;
  }
  NodeOrErr->print(Os, PrintingPolicy(Match.Context->getLangOpts()));
  *Result += Os.str();
  return Error::success();
}

Error evalData(const NodeRefData &Data, const MatchFinder::MatchResult &Match,
           std::string *Result) {
  auto NodeOrErr = getNode(Match.Nodes, Data.Id);
  if (auto Err = NodeOrErr.takeError()) {
    return Err;
  }
  *Result += fixit::getSourceAuto(NodeOrErr.get(), *Match.Context);
  return Error::success();
}

Error evalData(const MemberOpData &Data, const MatchFinder::MatchResult &Match,
           std::string *Result) {
  const auto *E = Match.Nodes.getNodeAs<Expr>(Data.ObjectId);
  if (E == nullptr) {
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Id not bound: " + Data.ObjectId);
  }
  if (!E->isImplicitCXXThis()) {
    *Result += E->getType()->isAnyPointerType()
                   ? fixit::formatArrow(*Match.Context, *E)
                   : fixit::formatDot(*Match.Context, *E);
  }
  return Data.Member.eval(Match, Result);
}

Error evalData(const ExprOpData &Data, const MatchFinder::MatchResult &Match,
           std::string *Result) {
  const auto *Expression = Match.Nodes.getNodeAs<Expr>(Data.Id);
  if (Expression == nullptr) {
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Id not bound: " + Data.Id);
  }
  const auto &Context = *Match.Context;
  switch (Data.Op) {
    case ExprOpData::Operator::kValue:
      if (Expression->getType()->isAnyPointerType()) {
        *Result += fixit::formatDereference(Context, *Expression);
      } else {
        *Result += fixit::getText(*Expression, Context);
      }
      break;
    case ExprOpData::Operator::kAddress:
      if (Expression->getType()->isAnyPointerType()) {
        *Result += fixit::getText(*Expression, Context);
      } else {
        *Result += fixit::formatAddressOf(Context, *Expression);
      }
      break;
    case ExprOpData::Operator::kParens:
      if (fixit::needsParens(*Expression)) {
        *Result += "(";
        *Result += fixit::getText(*Expression, Context);
        *Result += ")";
      } else {
        *Result += fixit::getText(*Expression, Context);
      }
      break;
  }
  return Error::success();
}

Error evalData(const NameOpData &Data, const MatchFinder::MatchResult &Match,
           std::string *Result) {
  const NamedDecl *Decl;
  if (const auto *Init = Match.Nodes.getNodeAs<CXXCtorInitializer>(Data.Id)) {
    Decl = Init->getMember();
    if (Decl == nullptr) {
      return llvm::make_error<StringError>(
          errc::invalid_argument, "non-member initializer: " + Data.Id);
    }
  } else {
    Decl = Match.Nodes.getNodeAs<NamedDecl>(Data.Id);
    if (Decl == nullptr) {
      return llvm::make_error<StringError>(
          errc::invalid_argument,
          "Id not bound or wrong type for Name op: " + Data.Id);
    }
  }
  // getIdentifier() guards the validity of getName().
  if (Decl->getIdentifier() == nullptr) {
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Decl is not identifier: " + Data.Id);
  }
  *Result += Decl->getName();
  return Error::success();
}

Error evalData(const ArgsOpData &Data, const MatchFinder::MatchResult &Match,
           std::string *Result) {
  const auto *CE = Match.Nodes.getNodeAs<CallExpr>(Data.Id);
  if (CE == nullptr) {
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Id not bound: " + Data.Id);
  }
  *Result += getArgumentsText(*CE, Match);
  return Error::success();
}

Error evalData(const StatementsOpData &Data,
               const MatchFinder::MatchResult &Match, std::string *Result) {
  if (const auto *CS = Match.Nodes.getNodeAs<CompoundStmt>(Data.Id)) {
    *Result += getStatementsText(*CS, Match);
    return Error::success();
  }
  if (const auto *S = Match.Nodes.getNodeAs<Stmt>(Data.Id)) {
    *Result += fixit::getSourceAuto(*S, *Match.Context);
    return Error::success();
  }
  return llvm::make_error<StringError>(errc::invalid_argument,
                                       "Id not bound: " + Data.Id);
}

Error evalData(const NodeFunctionOpData &Data,
           const MatchFinder::MatchResult &Match, std::string *Result) {
  auto NodeOrErr = getNode(Match.Nodes, Data.Id);
  if (auto Err = NodeOrErr.takeError()) {
    return Err;
  }
  *Result += Data.F(*NodeOrErr, *Match.Context);
  return Error::success();
}

Error evalData(const StringFunctionOpData &Data,
           const MatchFinder::MatchResult &Match, std::string *Result) {
  std::string PartResult;
  if (auto Err = Data.Part.eval(Match, &PartResult)) {
    return Err;
  }
  *Result += Data.F(PartResult);
  return Error::success();
}

template <typename T>
class StencilPartImpl : public StencilPartInterface {
 public:
  template <typename... Ps>
  explicit StencilPartImpl(Ps &&... Args)
      : StencilPartInterface(StencilPartImpl::typeId()),
        Data(std::forward<Ps>(Args)...) {}

  StencilPartImpl(const StencilPartImpl &) = default;
  StencilPartImpl(StencilPartImpl &&) = default;
  StencilPartImpl &operator=(const StencilPartImpl &) = default;
  StencilPartImpl &operator=(StencilPartImpl &&) = default;

  static const void* typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    return evalData(Data, Match, Result);
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<StencilPartImpl>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<StencilPartImpl>(&Other)) {
      return Data == OtherPtr->Data;
    }
    return false;
  }

 private:
  T Data;
};

using RawText = StencilPartImpl<RawTextData>;
using DebugPrintNodeOp = StencilPartImpl<DebugPrintNodeOpData>;
using NodeRef = StencilPartImpl<NodeRefData>;
using MemberOp = StencilPartImpl<MemberOpData>;
using ExprOp = StencilPartImpl<ExprOpData>;
using NameOp = StencilPartImpl<NameOpData>;
using ArgsOp = StencilPartImpl<ArgsOpData>;
using StatementsOp = StencilPartImpl<StatementsOpData>;
using NodeFunctionOp = StencilPartImpl<NodeFunctionOpData>;
using StringFunctionOp = StencilPartImpl<StringFunctionOpData>;
} // namespace

NodeId::NodeId() : NodeId(nextId()) {}

void Stencil::append(const NodeId &Id) {
  Parts.emplace_back(llvm::make_unique<NodeRef>(Id.id()));
}

void Stencil::append(StringRef Text) {
  Parts.emplace_back(llvm::make_unique<RawText>(Text));
}

void Stencil::concat(Stencil OtherStencil) {
  for (auto &Part : OtherStencil.Parts)
    Parts.push_back(std::move(Part));
  for (auto &AddedInclude : OtherStencil.AddedIncludes) {
    AddedIncludes.push_back(std::move(AddedInclude));
  }
  for (auto &RemovedInclude : OtherStencil.RemovedIncludes) {
    RemovedIncludes.push_back(std::move(RemovedInclude));
  }
}

llvm::Expected<std::string>
Stencil::eval(const MatchFinder::MatchResult &Match) const {
  std::string Result;
  for (const auto &Part : Parts) {
    if (auto Err = Part.eval(Match, &Result)) {
      return std::move(Err);
    }
  }
  return Result;
}

namespace stencil_generators {
StencilPart text(StringRef Text) {
  return StencilPart(llvm::make_unique<RawText>(Text));
}

StencilPart node(llvm::StringRef Id) {
  return StencilPart(llvm::make_unique<NodeRef>(Id));
}
StencilPart node(const NodeId &Id) { return node(Id.id()); }

StencilPart member(StringRef Id, StringRef Member) {
  return StencilPart(llvm::make_unique<MemberOp>(Id, text(Member)));
}
StencilPart member(const NodeId &ObjectId, StringRef Member) {
  return member(ObjectId.id(), Member);
}

StencilPart member(StringRef Id, StencilPart Member) {
  return StencilPart(llvm::make_unique<MemberOp>(Id, std::move(Member)));
}
StencilPart member(const NodeId &ObjectId, StencilPart Member) {
  return member(ObjectId.id(), std::move(Member));
}

StencilPart asValue(StringRef Id) {
  return StencilPart(
      llvm::make_unique<ExprOp>(ExprOpData::Operator::kValue, Id));
}
StencilPart asValue(const NodeId &Id) { return asValue(Id.id()); }

StencilPart asAddress(StringRef Id) {
  return StencilPart(
      llvm::make_unique<ExprOp>(ExprOpData::Operator::kAddress, Id));
}
StencilPart asAddress(const NodeId &Id) { return asAddress(Id.id()); }

StencilPart parens(StringRef Id) {
  return StencilPart(
      llvm::make_unique<ExprOp>(ExprOpData::Operator::kParens, Id));
}
StencilPart parens(const NodeId &Id) { return parens(Id.id()); }

StencilPart name(StringRef DeclId) {
  return StencilPart(llvm::make_unique<NameOp>(DeclId));
}
StencilPart name(const NodeId &DeclId) { return name(DeclId.id()); }

StencilPart apply(NodeFunction Fn, StringRef Id) {
  return StencilPart(llvm::make_unique<NodeFunctionOp>(std::move(Fn), Id));
}
StencilPart apply(NodeFunction Fn, const NodeId &Id) {
  return apply(std::move(Fn), Id.id());
}

StencilPart apply(StringFunction Fn, StencilPart Part) {
  return StencilPart(
      llvm::make_unique<StringFunctionOp>(std::move(Fn), std::move(Part)));
}
StencilPart apply(StringFunction Fn, llvm::StringRef Id) {
  return apply(std::move(Fn), node(Id));
}
StencilPart apply(StringFunction Fn, const NodeId &Id) {
  return apply(std::move(Fn), node(Id));
}

StencilPart args(StringRef CallId) {
  return StencilPart(llvm::make_unique<ArgsOp>(CallId));
}
StencilPart args(const NodeId &CallId) { return args(CallId.id()); }

StencilPart statements(llvm::StringRef StmtId) {
  return StencilPart(llvm::make_unique<StatementsOp>(StmtId));
}
StencilPart statements(const NodeId &StmtId) { return statements(StmtId.id()); }

StencilPart dPrint(StringRef Id) {
  return StencilPart(llvm::make_unique<DebugPrintNodeOp>(Id));
}
StencilPart dPrint(const NodeId &Id) { return dPrint(Id.id()); }

AddIncludeOp addInclude(StringRef Path) {
  return AddIncludeOp{std::string(Path)};
}
RemoveIncludeOp removeInclude(StringRef Path) {
  return RemoveIncludeOp{std::string(Path)};
}
} // namespace stencil_generators
} // namespace tooling
} // namespace clang
