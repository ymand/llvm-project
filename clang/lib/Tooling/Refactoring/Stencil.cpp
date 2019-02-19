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
class RawText : public StencilPartInterface {
public:
  explicit RawText(StringRef Text)
      : StencilPartInterface(RawText::typeId()), Text(Text) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &,
             std::string *Result) const override {
    Result->append(Text);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<RawText>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<RawText>(&Other)) {
      return Text == OtherPtr->Text;
    }
    return false;
  }

private:
  std::string Text;
};

// A debugging operation to dump the AST for a particular (bound) AST node.
class DebugPrintNodeOp : public StencilPartInterface {
public:
  explicit DebugPrintNodeOp(StringRef Id)
      : StencilPartInterface(DebugPrintNodeOp::typeId()), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    std::string Output;
    llvm::raw_string_ostream Os(Output);
    auto NodeOrErr = getNode(Match.Nodes, Id);
    if (auto Err = NodeOrErr.takeError()) {
      return Err;
    }
    NodeOrErr->print(Os, PrintingPolicy(Match.Context->getLangOpts()));
    *Result += Os.str();
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<DebugPrintNodeOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<DebugPrintNodeOp>(&Other)) {
      return Id == OtherPtr->Id;
    }
    return false;
  }

private:
  std::string Id;
};

// A reference to a particular (bound) AST node.
class NodeRef : public StencilPartInterface {
public:
  explicit NodeRef(StringRef Id)
      : StencilPartInterface(NodeRef::typeId()), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    auto NodeOrErr = getNode(Match.Nodes, Id);
    if (auto Err = NodeOrErr.takeError()) {
      return Err;
    }
    *Result += fixit::getSourceSmart(NodeOrErr.get(), *Match.Context);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<NodeRef>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<NodeRef>(&Other)) {
      return Id == OtherPtr->Id;
    }
    return false;
  }

private:
  std::string Id;
};

// A stencil operation that, given a reference to an expression e and a Part
// describing a member m, yields "e->m", when e is a pointer, "e2->m" when e =
// "*e2" and "e.m" otherwise.
class MemberOp : public StencilPartInterface {
public:
  MemberOp(StringRef ObjectId, StencilPart Member)
      : StencilPartInterface(MemberOp::typeId()), ObjectId(ObjectId),
        Member(std::move(Member)) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    const auto *E = Match.Nodes.getNodeAs<Expr>(ObjectId);
    if (E == nullptr) {
      return llvm::make_error<StringError>(errc::invalid_argument,
                                           "Id not bound: " + ObjectId);
    }
    if (!E->isImplicitCXXThis()) {
      *Result += E->getType()->isAnyPointerType()
                     ? fixit::formatArrow(*Match.Context, *E)
                     : fixit::formatDot(*Match.Context, *E);
    }
    return Member.eval(Match, Result);
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<MemberOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<MemberOp>(&Other)) {
      return ObjectId == OtherPtr->ObjectId && Member == OtherPtr->Member;
    }
    return false;
  }

private:
  std::string ObjectId;
  StencilPart Member;
};

// Operations all take a single reference to a Expr parameter, e.
class ExprOp : public StencilPartInterface {
public:
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

  ExprOp(Operator Op, StringRef Id)
      : StencilPartInterface(ExprOp::typeId()), Op(Op), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    const auto *Expression = Match.Nodes.getNodeAs<Expr>(Id);
    if (Expression == nullptr) {
      return llvm::make_error<StringError>(errc::invalid_argument,
                                           "Id not bound: " + Id);
    }
    const auto &Context = *Match.Context;
    switch (Op) {
    case ExprOp::Operator::kValue:
      if (Expression->getType()->isAnyPointerType()) {
        *Result += fixit::formatDereference(Context, *Expression);
      } else {
        *Result += fixit::getText(*Expression, Context);
      }
      break;
    case ExprOp::Operator::kAddress:
      if (Expression->getType()->isAnyPointerType()) {
        *Result += fixit::getText(*Expression, Context);
      } else {
        *Result += fixit::formatAddressOf(Context, *Expression);
      }
      break;
    case ExprOp::Operator::kParens:
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

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<ExprOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<ExprOp>(&Other)) {
      return Op == OtherPtr->Op && Id == OtherPtr->Id;
    }
    return false;
  }

private:
  Operator Op;
  std::string Id;
};

// Given a reference to a named declaration d (NamedDecl), yields
// the name. "d" must have an identifier name (that is, constructors are
// not valid arguments to the Name operation).
class NameOp : public StencilPartInterface {
public:
  explicit NameOp(StringRef Id)
      : StencilPartInterface(NameOp::typeId()), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    const NamedDecl *Decl;
    if (const auto *Init = Match.Nodes.getNodeAs<CXXCtorInitializer>(Id)) {
      Decl = Init->getMember();
      if (Decl == nullptr) {
        return llvm::make_error<StringError>(errc::invalid_argument,
                                             "non-member initializer: " + Id);
      }
    } else {
      Decl = Match.Nodes.getNodeAs<NamedDecl>(Id);
      if (Decl == nullptr) {
        return llvm::make_error<StringError>(
            errc::invalid_argument,
            "Id not bound or wrong type for Name op: " + Id);
      }
    }
    // getIdentifier() guards the validity of getName().
    if (Decl->getIdentifier() == nullptr) {
      return llvm::make_error<StringError>(errc::invalid_argument,
                                           "Decl is not identifier: " + Id);
    }
    *Result += Decl->getName();
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<NameOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<NameOp>(&Other)) {
      return Id == OtherPtr->Id;
    }
    return false;
  }

private:
  std::string Id;
};

// Given a reference to a call expression (CallExpr), yields the
// arguments as a comma separated list.
class ArgsOp : public StencilPartInterface {
public:
  explicit ArgsOp(StringRef Id)
      : StencilPartInterface(ArgsOp::typeId()), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    const auto *CE = Match.Nodes.getNodeAs<CallExpr>(Id);
    if (CE == nullptr) {
      return llvm::make_error<StringError>(errc::invalid_argument,
                                           "Id not bound: " + Id);
    }
    *Result += getArgumentsText(*CE, Match);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<ArgsOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<ArgsOp>(&Other)) {
      return Id == OtherPtr->Id;
      std::string Id;
    };
    return false;
  }

private:
  std::string Id;
};

// Given a reference to a statement, yields the contents between the braces,
// if it is compound, or the statement and its trailing semicolon (if any)
// otherwise.
class StatementsOp : public StencilPartInterface {
public:
  explicit StatementsOp(StringRef Id)
      : StencilPartInterface(ArgsOp::typeId()), Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }
  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    if (const auto *CS = Match.Nodes.getNodeAs<CompoundStmt>(Id)) {
      *Result += getStatementsText(*CS, Match);
      return Error::success();
    }
    if (const auto *S = Match.Nodes.getNodeAs<Stmt>(Id)) {
      *Result += fixit::getSourceSmart(*S, *Match.Context);
      return Error::success();
    }
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Id not bound: " + Id);
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<StatementsOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    if (const auto *OtherPtr = down_cast<StatementsOp>(&Other)) {
      return Id == OtherPtr->Id;
      std::string Id;
    };
    return false;
  }

private:
  std::string Id;
};

// Given a function and a reference to a node, yields the string that
// results from applying the function to the referenced node.
class NodeFunctionOp : public StencilPartInterface {
public:
  NodeFunctionOp(stencil_generators::NodeFunction F, StringRef Id)
      : StencilPartInterface(NodeFunctionOp::typeId()), F(std::move(F)),
        Id(Id) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    auto NodeOrErr = getNode(Match.Nodes, Id);
    if (auto Err = NodeOrErr.takeError()) {
      return Err;
    }
    *Result += F(*NodeOrErr, *Match.Context);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<NodeFunctionOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    return false;
  }

private:
  stencil_generators::NodeFunction F;
  std::string Id;
};

// Given a function and a stencil part, yields the string that results from
// applying the function to the part's evaluation.
class StringFunctionOp : public StencilPartInterface {
public:
  StringFunctionOp(stencil_generators::StringFunction F, StencilPart Part)
      : StencilPartInterface(StringFunctionOp::typeId()), F(std::move(F)),
        Part(std::move(Part)) {}

  static const void *typeId() {
    static bool b;
    return &b;
  }

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    std::string PartResult;
    if (auto Err = Part.eval(Match, &PartResult)) {
      return Err;
    }
    *Result += F(PartResult);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<StringFunctionOp>(*this);
  }

  bool isEqual(const StencilPartInterface &Other) const override {
    return false;
  }

private:
  stencil_generators::StringFunction F;
  StencilPart Part;
};
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
  return StencilPart(llvm::make_unique<ExprOp>(ExprOp::Operator::kValue, Id));
}
StencilPart asValue(const NodeId &Id) { return asValue(Id.id()); }

StencilPart asAddress(StringRef Id) {
  return StencilPart(llvm::make_unique<ExprOp>(ExprOp::Operator::kAddress, Id));
}
StencilPart asAddress(const NodeId &Id) { return asAddress(Id.id()); }

StencilPart parens(StringRef Id) {
  return StencilPart(llvm::make_unique<ExprOp>(ExprOp::Operator::kParens, Id));
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
