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
//
// BEGIN Utilities -- the folowing functions all belong in a separate utilities
// library.  We include them here for the purposes of this demo so that it will
// compile
//

// Returns true if expr needs to be put in parens when it is the target
// of a dot or arrow, i.e. when it is an operator syntactically.
static bool needParensBeforeDotOrArrow(const clang::Expr &Expr) {
  // We always want parens around unary, binary, and ternary operators.
  if (llvm::dyn_cast<clang::UnaryOperator>(&Expr) ||
      llvm::dyn_cast<clang::BinaryOperator>(&Expr) ||
      llvm::dyn_cast<clang::ConditionalOperator>(&Expr)) {
    return true;
  }

  // We need parens around calls to all overloaded operators except for function
  // calls, subscripts, and expressions that are already part of an implicit
  // call to operator->.
  if (const auto *Op = llvm::dyn_cast<clang::CXXOperatorCallExpr>(&Expr)) {
    return Op->getOperator() != clang::OO_Call &&
           Op->getOperator() != clang::OO_Subscript &&
           Op->getOperator() != clang::OO_Arrow;
  }

  return false;
}

// BEGIN from clang-tidy/readability/RedundantStringCStrCheck.cpp

// Return true if expr needs to be put in parens when it is an argument of a
// prefix unary operator, e.g. when it is a binary or ternary operator
// syntactically.
static bool needParensAfterUnaryOperator(const Expr &ExprNode) {
  if (isa<clang::BinaryOperator>(&ExprNode) ||
      isa<clang::ConditionalOperator>(&ExprNode)) {
    return true;
  }
  if (const auto *Op = dyn_cast<CXXOperatorCallExpr>(&ExprNode)) {
    return Op->getNumArgs() == 2 && Op->getOperator() != OO_PlusPlus &&
           Op->getOperator() != OO_MinusMinus && Op->getOperator() != OO_Call &&
           Op->getOperator() != OO_Subscript;
  }
  return false;
}

// Format a pointer to an expression: prefix with '*' but simplify
// when it already begins with '&'.  Return empty string on failure.
static std::string formatDereference(const ASTContext &Context,
                                     const Expr &ExprNode) {
  if (const auto *Op = dyn_cast<clang::UnaryOperator>(&ExprNode)) {
    if (Op->getOpcode() == UO_AddrOf) {
      // Strip leading '&'.
      return tooling::fixit::getText(*Op->getSubExpr()->IgnoreParens(),
                                     Context);
    }
  }
  StringRef Text = tooling::fixit::getText(ExprNode, Context);

  if (Text.empty())
    return std::string();
  // Add leading '*'.
  if (needParensAfterUnaryOperator(ExprNode)) {
    return (llvm::Twine("*(") + Text + ")").str();
  }
  return (llvm::Twine("*") + Text).str();
}

// END from clang-tidy/readability/RedundantStringCStrCheck.cpp

// Format a pointer to an expression: prefix with '&' but simplify when it
// already begins with '*'.  Returns empty string on failure.
static std::string formatAddressOf(const ASTContext &Context,
                            const clang::Expr &Expr) {
  if (const auto *Op = llvm::dyn_cast<clang::UnaryOperator>(&Expr)) {
    if (Op->getOpcode() == clang::UO_Deref) {
      // Strip leading '*'.
      return tooling::fixit::getText(*Op->getSubExpr()->IgnoreParens(),
                                     Context);
    }
  }
  // Add leading '&'.
  const std::string Text = fixit::getText(Expr, Context);
  if (Text.empty())
    return std::string();
  if (needParensAfterUnaryOperator(Expr)) {
    return (llvm::Twine("&(") + Text + ")").str();
  }
  return (llvm::Twine("&") + Text).str();
}

static std::string formatDot(const ASTContext &Context,
                             const clang::Expr &Expr) {
  if (const auto *Op = llvm::dyn_cast<clang::UnaryOperator>(&Expr)) {
    if (Op->getOpcode() == clang::UO_Deref) {
      // Strip leading '*', add following '->'.
      const clang::Expr *SubExpr = Op->getSubExpr()->IgnoreParenImpCasts();
      const std::string DerefText = fixit::getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ")->").str();
      }
      return (llvm::Twine(DerefText) + "->").str();
    }
  }
  // Add following '.'.
  const std::string Text = fixit::getText(Expr, Context);
  if (Text.empty())
    return std::string();
  if (needParensBeforeDotOrArrow(Expr)) {
    return (llvm::Twine("(") + Text + ").").str();
  }
  return (llvm::Twine(Text) + ".").str();
}

static std::string formatArrow(const ASTContext &Context,
                               const clang::Expr &Expr) {
  if (const auto *Op = llvm::dyn_cast<clang::UnaryOperator>(&Expr)) {
    if (Op->getOpcode() == clang::UO_AddrOf) {
      // Strip leading '&', add following '.'.
      const clang::Expr *SubExpr = Op->getSubExpr()->IgnoreParenImpCasts();
      const std::string DerefText = fixit::getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ").").str();
      }
      return (llvm::Twine(DerefText) + ".").str();
    }
  }
  // Add following '->'.
  const std::string Text = fixit::getText(Expr, Context);
  if (Text.empty())
    return std::string();
  if (needParensBeforeDotOrArrow(Expr)) {
    return (llvm::Twine("(") + Text + ")->").str();
  }
  return (llvm::Twine(Text) + "->").str();
}

// BEGIN from: clang-tidy/utils/LexerUtils.cpp
static SourceLocation findPreviousTokenStart(SourceLocation Start,
                                             const SourceManager &SM,
                                             const LangOptions &LangOpts) {
  if (Start.isInvalid() || Start.isMacroID())
    return SourceLocation();

  SourceLocation BeforeStart = Start.getLocWithOffset(-1);
  if (BeforeStart.isInvalid() || BeforeStart.isMacroID())
    return SourceLocation();

  return Lexer::GetBeginningOfToken(BeforeStart, SM, LangOpts);
}

static SourceLocation findPreviousTokenKind(SourceLocation Start,
                                            const SourceManager &SM,
                                            const LangOptions &LangOpts,
                                            tok::TokenKind TK) {
  while (true) {
    SourceLocation L = findPreviousTokenStart(Start, SM, LangOpts);
    if (L.isInvalid() || L.isMacroID())
      return SourceLocation();

    Token T;
    if (Lexer::getRawToken(L, T, SM, LangOpts, /*IgnoreWhiteSpace=*/true))
      return SourceLocation();

    if (T.is(TK))
      return T.getLocation();

    Start = L;
  }
}
// END From: clang-tidy/utils/LexerUtils

// For refactoring purposes, some expressions should be wrapped in parentheses
// to avoid changes in the order of operation, assuming no other information
// about the surrounding context.
static bool needsParens(const Expr *E) {
  return isa<BinaryOperator>(E) || isa<UnaryOperator>(E) ||
         isa<CXXOperatorCallExpr>(E) || isa<AbstractConditionalOperator>(E);
}

// Finds the open paren of the call expression and return its location.  Returns
// an invalid location if not found.
static SourceLocation
getOpenParen(const CallExpr &E,
             const ast_matchers::MatchFinder::MatchResult &Result) {
  SourceLocation EndLoc =
      E.getNumArgs() == 0 ? E.getRParenLoc() : E.getArg(0)->getBeginLoc();
  return findPreviousTokenKind(EndLoc, *Result.SourceManager,
                               Result.Context->getLangOpts(),
                               tok::TokenKind::l_paren);
}

// For a given range, returns the lexed token immediately after the range if
// and only if it's a semicolon.
static Optional<Token> getTrailingSemi(SourceLocation EndLoc,
                                       const ASTContext &Context) {
  if (Optional<Token> Next = Lexer::findNextToken(
          EndLoc, Context.getSourceManager(), Context.getLangOpts())) {
    return Next->is(clang::tok::TokenKind::semi) ? Next : None;
  }
  return None;
}

static const clang::Stmt *getStatementParent(const clang::Stmt &node,
                                             ASTContext &context) {
  using namespace ast_matchers;

  auto is_or_has_node =
      anyOf(equalsNode(&node), hasDescendant(equalsNode(&node)));
  auto not_in_condition = unless(hasCondition(is_or_has_node));
  // Note that SwitchCase nodes have the subsequent statement as substatement.
  // For example, in "case 1: a(); b();", a() will be the child of the
  // SwitchCase "case 1:".
  // TODO(djasper): Also handle other labels, probably not important in google3.
  // missing: switchStmt() (although this is a weird corner case).
  auto statement = stmt(hasParent(
      stmt(anyOf(compoundStmt(), whileStmt(not_in_condition),
                 doStmt(not_in_condition), switchCase(),
                 ifStmt(not_in_condition),
                 forStmt(not_in_condition, unless(hasIncrement(is_or_has_node)),
                         unless(hasLoopInit(is_or_has_node)))))
          .bind("parent")));
  return selectFirst<const clang::Stmt>("parent",
                                        match(statement, node, context));
}

// Is a real statement (not an expression inside another expression). That is,
// not an expression with an expression parent.
static bool isRealStatement(const Stmt &S, ASTContext &Context) {
  return !isa<Expr>(S) || getStatementParent(S, Context) != nullptr;
}

// For all non-expression statements, extend the source to include any trailing
// semi. Returns a SourceRange representing a token range.
static SourceRange getTokenRange(const Stmt &S, ASTContext &Context) {
  // Only exlude non-statement expressions.
  if (isRealStatement(S, Context)) {
    // TODO: exclude case where last token is a right brace?
    if (auto Tok = getTrailingSemi(S.getEndLoc(), Context))
      return SourceRange(S.getBeginLoc(), Tok->getLocation());
  }
  return S.getSourceRange();
}

static SourceRange getTokenRange(const ast_type_traits::DynTypedNode &Node,
                                 ASTContext &Context) {
  if (const auto *S = Node.get<Stmt>())
    return getTokenRange(*S, Context);
  return Node.getSourceRange();
}

template <typename T>
StringRef getText(const T &Node, ASTContext &Context) {
  return Lexer::getSourceText(
      CharSourceRange::getTokenRange(getTokenRange(Node, Context)),
      Context.getSourceManager(), Context.getLangOpts());
}

//
// END Utilities
//

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
  auto Range = CharSourceRange::getCharRange(
      getOpenParen(CE, Result).getLocWithOffset(1), CE.getRParenLoc());
  return Lexer::getSourceText(Range, Result.Context->getSourceManager(),
                              Result.Context->getLangOpts());
}

// Gets the source text of the statements in the compound statement. Includes
// all source between the braces.
static StringRef
getStatementsText(const CompoundStmt &CS,
                  const ast_matchers::MatchFinder::MatchResult &Result) {
  auto Range = CharSourceRange::getCharRange(
      CS.getLBracLoc().getLocWithOffset(1), CS.getRBracLoc());
  return Lexer::getSourceText(Range, Result.Context->getSourceManager(),
                              Result.Context->getLangOpts());
}

static Expected<ast_type_traits::DynTypedNode>
getNode(const ast_matchers::BoundNodes &Nodes, llvm::StringRef Id) {
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
using ::llvm::StringRef;

// An arbitrary fragment of code within a stencil.
class RawText : public StencilPartInterface {
public:
  explicit RawText(StringRef Text) : Text(Text) {}

  Error eval(const MatchFinder::MatchResult &,
             std::string *Result) const override {
    Result->append(Text);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<RawText>(*this);
  }

private:
  std::string Text;
};

// A debugging operation to dump the AST for a particular (bound) AST node.
class DebugPrintNodeOp : public StencilPartInterface {
public:
  explicit DebugPrintNodeOp(StringRef Id) : Id(Id) {}

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

private:
  std::string Id;
};

// A reference to a particular (bound) AST node.
class NodeRef : public StencilPartInterface {
public:
  explicit NodeRef(StringRef Id) : Id(Id) {}

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    auto NodeOrErr = getNode(Match.Nodes, Id);
    if (auto Err = NodeOrErr.takeError()) {
      return Err;
    }
    *Result += getText(NodeOrErr.get(), *Match.Context);
    return Error::success();
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<NodeRef>(*this);
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
      : ObjectId(ObjectId), Member(std::move(Member)) {}

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    const auto *E = Match.Nodes.getNodeAs<Expr>(ObjectId);
    if (E == nullptr) {
      return llvm::make_error<StringError>(errc::invalid_argument,
                                           "Id not bound: " + ObjectId);
    }
    // N.B. The RHS is a google string. TODO(yitzhakm): fix the RHS to be a
    // std::string.
    if (!E->isImplicitCXXThis()) {
      *Result += E->getType()->isAnyPointerType()
                     ? formatArrow(*Match.Context, *E)
                     : formatDot(*Match.Context, *E);
    }
    return Member.eval(Match, Result);
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<MemberOp>(*this);
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

  ExprOp(Operator Op, StringRef Id) : Op(Op), Id(Id) {}

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
        *Result += formatDereference(Context, *Expression);
      } else {
        *Result += fixit::getText(*Expression, Context);
      }
      break;
    case ExprOp::Operator::kAddress:
      if (Expression->getType()->isAnyPointerType()) {
        *Result += fixit::getText(*Expression, Context);
      } else {
        *Result += formatAddressOf(Context, *Expression);
      }
      break;
    case ExprOp::Operator::kParens:
      if (needsParens(Expression)) {
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

private:
  Operator Op;
  std::string Id;
};

// Given a reference to a named declaration d (NamedDecl), yields
// the name. "d" must have an identifier name (that is, constructors are
// not valid arguments to the Name operation).
class NameOp : public StencilPartInterface {
public:
  explicit NameOp(StringRef Id) : Id(Id) {}

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

private:
  std::string Id;
};

// Given a reference to a call expression (CallExpr), yields the
// arguments as a comma separated list.
class ArgsOp : public StencilPartInterface {
public:
  explicit ArgsOp(StringRef Id) : Id(Id) {}

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

private:
  std::string Id;
};

// Given a reference to a statement, yields the contents between the braces, if
// it is compound, or the statement and its trailing semicolon (if any)
// otherwise.
class StatementsOp : public StencilPartInterface {
public:
  explicit StatementsOp(StringRef Id) : Id(Id) {}

  Error eval(const MatchFinder::MatchResult &Match,
             std::string *Result) const override {
    if (const auto *CS = Match.Nodes.getNodeAs<CompoundStmt>(Id)) {
      *Result += getStatementsText(*CS, Match);
      return Error::success();
    }
    if (const auto *S = Match.Nodes.getNodeAs<Stmt>(Id)) {
      *Result += getText(*S, *Match.Context);
      return Error::success();
    }
    return llvm::make_error<StringError>(errc::invalid_argument,
                                         "Id not bound: " + Id);
  }

  std::unique_ptr<StencilPartInterface> clone() const override {
    return llvm::make_unique<StatementsOp>(*this);
  }

private:
  std::string Id;
};

// Given a function and a reference to a node, yields the string that results
// from applying the function to the referenced node.
class NodeFunctionOp : public StencilPartInterface {
public:
  NodeFunctionOp(stencil_generators::NodeFunction F, StringRef Id)
      : F(std::move(F)), Id(Id) {}

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

private:
  stencil_generators::NodeFunction F;
  std::string Id;
};

// Given a function and a stencil part, yields the string that results from
// applying the function to the part's evaluation.
class StringFunctionOp : public StencilPartInterface {
public:
  StringFunctionOp(stencil_generators::StringFunction F, StencilPart Part)
      : F(std::move(F)), Part(std::move(Part)) {}

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
