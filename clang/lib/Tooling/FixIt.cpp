//===--- FixIt.cpp - FixIt Hint utilities -----------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains implementations of utitilies to ease source code rewriting
// by providing helper functions related to FixItHint, source location analysis
// and source generation.
//
//===----------------------------------------------------------------------===//
#include "clang/Tooling/FixIt.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Lex/Lexer.h"

namespace clang {
namespace tooling {
namespace fixit {

namespace internal {
StringRef getText(CharSourceRange Range, const ASTContext &Context) {
  return Lexer::getSourceText(Range, Context.getSourceManager(),
                              Context.getLangOpts());
}
} // end namespace internal

SourceLocation findPreviousTokenStart(SourceLocation Start,
                                      const SourceManager &SM,
                                      const LangOptions &LangOpts) {
  if (Start.isInvalid() || Start.isMacroID())
    return SourceLocation();

  SourceLocation BeforeStart = Start.getLocWithOffset(-1);
  if (BeforeStart.isInvalid() || BeforeStart.isMacroID())
    return SourceLocation();

  return Lexer::GetBeginningOfToken(BeforeStart, SM, LangOpts);
}

SourceLocation findPreviousTokenKind(SourceLocation Start,
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

bool needsParens(const Expr &E) {
  return isa<BinaryOperator>(E) || isa<UnaryOperator>(E) ||
         isa<CXXOperatorCallExpr>(E) || isa<AbstractConditionalOperator>(E);
}

// Returns true if expr needs to be put in parens to be parsed correctly when it
// is the target of a dot or arrow. For example, `*x` needs parens in this
// context or the resulting expression will be misparsed: `*x.f` is parsed as
// `*(x.f)` while the intent is `(*x).f`.
static bool needsParensBeforeDotOrArrow(const Expr &Expr) {
  // We always want parens around unary, binary, and ternary operators.
  if (dyn_cast<UnaryOperator>(&Expr) || dyn_cast<BinaryOperator>(&Expr) ||
      dyn_cast<ConditionalOperator>(&Expr)) {
    return true;
  }

  // We need parens around calls to all overloaded operators except for function
  // calls, subscripts, and expressions that are already part of an implicit
  // call to operator->.
  if (const auto *Op = dyn_cast<CXXOperatorCallExpr>(&Expr)) {
    return Op->getOperator() != OO_Call && Op->getOperator() != OO_Subscript &&
           Op->getOperator() != OO_Arrow;
  }

  return false;
}

// Returns true if expr needs to be put in parens to be parsed correctly when it
// is the operand of a unary operator; for example, when it is a binary or
// ternary operator syntactically.
static bool needsParensAfterUnaryOperator(const Expr &ExprNode) {
  if (isa<BinaryOperator>(&ExprNode) || isa<ConditionalOperator>(&ExprNode)) {
    return true;
  }
  if (const auto *Op = dyn_cast<CXXOperatorCallExpr>(&ExprNode)) {
    return Op->getNumArgs() == 2 && Op->getOperator() != OO_PlusPlus &&
           Op->getOperator() != OO_MinusMinus && Op->getOperator() != OO_Call &&
           Op->getOperator() != OO_Subscript;
  }
  return false;
}

std::string formatDereference(const ASTContext &Context, const Expr &ExprNode) {
  if (const auto *Op = dyn_cast<UnaryOperator>(&ExprNode)) {
    if (Op->getOpcode() == UO_AddrOf) {
      // Strip leading '&'.
      return getText(*Op->getSubExpr()->IgnoreParens(), Context);
    }
  }
  StringRef Text = getText(ExprNode, Context);

  if (Text.empty())
    return std::string();
  // Add leading '*'.
  if (needsParensAfterUnaryOperator(ExprNode)) {
    return (llvm::Twine("*(") + Text + ")").str();
  }
  return (llvm::Twine("*") + Text).str();
}

std::string formatAddressOf(const ASTContext &Context, const Expr &ExprNode) {
  if (const auto *Op = dyn_cast<UnaryOperator>(&ExprNode)) {
    if (Op->getOpcode() == UO_Deref) {
      // Strip leading '*'.
      return getText(*Op->getSubExpr()->IgnoreParens(), Context);
    }
  }
  // Add leading '&'.
  const std::string Text = getText(ExprNode, Context);
  if (Text.empty())
    return std::string();
  if (needsParensAfterUnaryOperator(ExprNode)) {
    return (llvm::Twine("&(") + Text + ")").str();
  }
  return (llvm::Twine("&") + Text).str();
}

std::string formatDot(const ASTContext &Context, const Expr &ExprNode) {
  if (const auto *Op = llvm::dyn_cast<UnaryOperator>(&ExprNode)) {
    if (Op->getOpcode() == UO_Deref) {
      // Strip leading '*', add following '->'.
      const Expr *SubExpr = Op->getSubExpr()->IgnoreParenImpCasts();
      const std::string DerefText = getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needsParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ")->").str();
      }
      return (llvm::Twine(DerefText) + "->").str();
    }
  }
  // Add following '.'.
  const std::string Text = getText(ExprNode, Context);
  if (Text.empty())
    return std::string();
  if (needsParensBeforeDotOrArrow(ExprNode)) {
    return (llvm::Twine("(") + Text + ").").str();
  }
  return (llvm::Twine(Text) + ".").str();
}

std::string formatArrow(const ASTContext &Context, const Expr &ExprNode) {
  if (const auto *Op = llvm::dyn_cast<UnaryOperator>(&ExprNode)) {
    if (Op->getOpcode() == UO_AddrOf) {
      // Strip leading '&', add following '.'.
      const Expr *SubExpr = Op->getSubExpr()->IgnoreParenImpCasts();
      const std::string DerefText = getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needsParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ").").str();
      }
      return (llvm::Twine(DerefText) + ".").str();
    }
  }
  // Add following '->'.
  const std::string Text = getText(ExprNode, Context);
  if (Text.empty())
    return std::string();
  if (needsParensBeforeDotOrArrow(ExprNode)) {
    return (llvm::Twine("(") + Text + ")->").str();
  }
  return (llvm::Twine(Text) + "->").str();
}

SourceLocation findOpenParen(const CallExpr &E, const SourceManager &SM,
                             const LangOptions &LangOpts) {
  SourceLocation EndLoc =
      E.getNumArgs() == 0 ? E.getRParenLoc() : E.getArg(0)->getBeginLoc();
  return findPreviousTokenKind(EndLoc, SM, LangOpts, tok::TokenKind::l_paren);
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
  // FIXME: Also handle other labels.
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
static bool isNonSubexprStatement(const Stmt &S, ASTContext &Context) {
  return !isa<Expr>(S) || getStatementParent(S, Context) != nullptr;
}

CharSourceRange getSourceRangeAuto(const Stmt &S, ASTContext &Context) {
  // Only exlude non-statement expressions.
  if (isNonSubexprStatement(S, Context)) {
    // TODO: exclude case where last token is a right brace?
    if (auto Tok = getTrailingSemi(S.getEndLoc(), Context))
      return CharSourceRange::getTokenRange(S.getBeginLoc(),
                                            Tok->getLocation());
  }
  return CharSourceRange::getTokenRange(S.getSourceRange());
}

CharSourceRange getSourceRangeAuto(const ast_type_traits::DynTypedNode &Node,
                                   ASTContext &Context) {
  if (const auto *S = Node.get<Stmt>())
    return getSourceRangeAuto(*S, Context);
  return CharSourceRange::getTokenRange(Node.getSourceRange());
}

} // end namespace fixit
} // end namespace tooling
} // end namespace clang
