//===--- FixIt.cpp - FixIt Hint utilities -----------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file contains implementations of utitilies to ease source code rewriting
// by providing helper functions related to FixItHint.
//
//===----------------------------------------------------------------------===//
#include "clang/Tooling/FixIt.h"
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

CharSourceRange maybeExtendRange(CharSourceRange Range, tok::TokenKind Next,
                                 ASTContext &Context) {
  Optional<Token> Tok = Lexer::findNextToken(
      Range.getEnd(), Context.getSourceManager(), Context.getLangOpts());
  if (!Tok || !Tok->is(Next))
    return Range;
  return CharSourceRange::getTokenRange(Range.getBegin(), Tok->getLocation());
}
} // namespace internal

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
      return fixit::getText(*Op->getSubExpr()->IgnoreParens(), Context);
    }
  }
  StringRef Text = fixit::getText(ExprNode, Context);

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
      return fixit::getText(*Op->getSubExpr()->IgnoreParens(), Context);
    }
  }
  // Add leading '&'.
  const std::string Text = fixit::getText(ExprNode, Context);
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
      const std::string DerefText = fixit::getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needsParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ")->").str();
      }
      return (llvm::Twine(DerefText) + "->").str();
    }
  }
  // Add following '.'.
  const std::string Text = fixit::getText(ExprNode, Context);
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
      const std::string DerefText = fixit::getText(*SubExpr, Context);
      if (DerefText.empty())
        return std::string();
      if (needsParensBeforeDotOrArrow(*SubExpr)) {
        return (llvm::Twine("(") + DerefText + ").").str();
      }
      return (llvm::Twine(DerefText) + ".").str();
    }
  }
  // Add following '->'.
  const std::string Text = fixit::getText(ExprNode, Context);
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
} // end namespace fixit
} // end namespace tooling
} // end namespace clang
