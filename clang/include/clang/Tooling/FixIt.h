//===--- FixIt.h - FixIt Hint utilities -------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements functions to ease source rewriting from AST-nodes.
//
//  Example swapping A and B expressions:
//
//    Expr *A, *B;
//    tooling::fixit::createReplacement(*A, *B);
//    tooling::fixit::createReplacement(*B, *A);
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLING_FIXIT_H
#define LLVM_CLANG_TOOLING_FIXIT_H

#include "clang/AST/ASTContext.h"

namespace clang {
namespace tooling {
namespace fixit {

namespace internal {
StringRef getText(SourceRange Range, const ASTContext &Context);

/// Returns the SourceRange of a SourceRange. This identity function is
///        used by the following template abstractions.
inline SourceRange getSourceRange(const SourceRange &Range) { return Range; }

/// Returns the SourceRange of the token at Location \p Loc.
inline SourceRange getSourceRange(const SourceLocation &Loc) {
  return SourceRange(Loc);
}

/// Returns the SourceRange of an given Node. \p Node is typically a
///        'Stmt', 'Expr' or a 'Decl'.
template <typename T> SourceRange getSourceRange(const T &Node) {
  return Node.getSourceRange();
}
} // end namespace internal

// Returns a textual representation of \p Node.
template <typename T>
StringRef getText(const T &Node, const ASTContext &Context) {
  return internal::getText(internal::getSourceRange(Node), Context);
}

// Returns a FixItHint to remove \p Node.
// TODO: Add support for related syntactical elements (i.e. comments, ...).
template <typename T> FixItHint createRemoval(const T &Node) {
  return FixItHint::CreateRemoval(internal::getSourceRange(Node));
}

// Returns a FixItHint to replace \p Destination by \p Source.
template <typename D, typename S>
FixItHint createReplacement(const D &Destination, const S &Source,
                                   const ASTContext &Context) {
  return FixItHint::CreateReplacement(internal::getSourceRange(Destination),
                                      getText(Source, Context));
}

// Returns a FixItHint to replace \p Destination by \p Source.
template <typename D>
FixItHint createReplacement(const D &Destination, StringRef Source) {
  return FixItHint::CreateReplacement(internal::getSourceRange(Destination),
                                      Source);
}

// Finds the start location of the first token starting before `Start`. Returns
// an invalid location if no previous token is found.
SourceLocation findPreviousTokenStart(SourceLocation Start,
                                      const SourceManager &SM,
                                      const LangOptions &LangOpts);

// Finds the start location of the first token of the given kind starting before
// `Start`. Returns an invalid location if none is found.
SourceLocation findPreviousTokenKind(SourceLocation Start,
                                     const SourceManager &SM,
                                     const LangOptions &LangOpts,
                                     tok::TokenKind TK);

// Finds the open paren of the call expression and return its location. Returns
// an invalid location if no open paren is found.
SourceLocation findOpenParen(const CallExpr &E, const SourceManager &SM,
                             const LangOptions &LangOpts);

// Conservatively estimates whether the given expression should be wrapped in
// parentheses when printing (to avoid misinterpretation during parsing),
// assuming no other information about the surrounding context.
bool needsParens(const Expr &E);

// Returns true if expr needs to be put in parens to be parsed correctly when it
// is the target of a dot or arrow. For example, `*x` needs parens in this
// context or the resulting expression will be misparsed: `*x.f` is parsed as
// `*(x.f)` while the intent is `(*x).f`.
bool needParensBeforeDotOrArrow(const Expr &Expr);

// Returns true if expr needs to be put in parens to be parsed correctly when it
// is the operand of a unary operator; for example, when it is a binary or
// ternary operator syntactically.
bool needParensAfterUnaryOperator(const Expr &ExprNode);

// Formats a pointer to an expression: prefix with '*' but simplify when it
// already begins with '&'.  Return empty string on failure.
std::string formatDereference(const ASTContext &Context, const Expr &ExprNode);

// Formats a pointer to an expression: prefix with '&' but simplify when it
// already begins with '*'.  Returns empty string on failure.
std::string formatAddressOf(const ASTContext &Context, const Expr &Expr);

// Adds a dot to the end of the given expression, but adds parentheses when
// needed by the syntax, and simplifies to `->` when possible, e.g.:
//
//  x becomes x.
//  *a becomes a->
//  a+b becomes (a+b).
std::string formatDot(const ASTContext &Context, const Expr &Expr);

// Adds an arrow to the end of the given expression, but adds parentheses
// when needed by the syntax, and simplifies to `.` when possible, e.g.:
//
//  x becomes x->
//  &a becomes a.
//  a+b becomes (a+b)->
std::string formatArrow(const ASTContext &Context, const Expr &Expr);

} // end namespace fixit
} // end namespace tooling
} // end namespace clang

#endif // LLVM_CLANG_TOOLING_FIXINT_H
