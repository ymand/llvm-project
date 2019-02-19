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
#include "clang/Basic/TokenKinds.h"

namespace clang {
namespace tooling {
namespace fixit {

namespace internal {
StringRef getText(CharSourceRange Range, const ASTContext &Context);

/// Returns the token CharSourceRange corresponding to \p Range.
inline CharSourceRange getSourceRange(const SourceRange &Range) {
  return CharSourceRange::getTokenRange(Range);
}

/// Returns the CharSourceRange of the token at Location \p Loc.
inline CharSourceRange getSourceRange(const SourceLocation &Loc) {
  return CharSourceRange::getTokenRange(Loc, Loc);
}

/// Returns the CharSourceRange of an given Node. \p Node is typically a
///        'Stmt', 'Expr' or a 'Decl'.
template <typename T> CharSourceRange getSourceRange(const T &Node) {
  return CharSourceRange::getTokenRange(Node.getSourceRange());
}

/// Extends \p Range to include the token \p Next, if it immediately follows the
/// end of the range. Otherwise, returns \p Range unchanged.
CharSourceRange maybeExtendRange(CharSourceRange Range, tok::TokenKind Next,
                                 ASTContext &Context);
} // end namespace internal

/// Returns a textual representation of \p Node.
template <typename T>
StringRef getText(const T &Node, const ASTContext &Context) {
  return internal::getText(
      CharSourceRange::getTokenRange(internal::getSourceRange(Node)), Context);
}

// For statements that aren't subexpressions, returns a \p SourceRange that
// includes the statement's source and any trailing semi.
CharSourceRange getSourceRangeSmart(const Stmt &S, ASTContext &Context);

// For all clang::Stmts that are direct children of a compound statement,
// extends the source to include any trailing semi. Returns a SourceRange
// representing a token range.
CharSourceRange getSourceRangeSmart(const ast_type_traits::DynTypedNode &Node,
                                    ASTContext &Context);

// Get the source text of the node, taking into account the node's type and
// context. In contrast with getText(), this function selects a source range
// "smartly", extracting text that a reader might intuitively associate with a
// node.  Currently, only specialized for clang::Stmt, where it will include the
// trailing semicolon if the node is an entire sub statement of a compound
// statement.
//
// FIXME: choose a better name.
template <typename T>
StringRef getSourceSmart(const T &Node, ASTContext &Context) {
  return internal::getText(getSourceRangeSmart(Node, Context), Context);
}

/// Returns the source range spanning the node, extended to include \p Next, if
/// it immediately follows \p Node. Otherwise, returns the normal range of \p
/// Node.  See comments on `getExtendedText()` for examples.
template <typename T>
CharSourceRange getExtendedRange(const T &Node, tok::TokenKind Next,
                                 ASTContext &Context) {
  return internal::maybeExtendRange(internal::getSourceRange(Node), Next,
                                    Context);
}

/// Returns the source text of the node, extended to include \p Next, if it
/// immediately follows the node. Otherwise, returns the text of just \p Node.
///
/// For example, given statements S1 and S2 below:
/// \code
///   {
///     // S1:
///     if (!x) return foo();
///     // S2:
///     if (!x) { return 3; }
///   }
/// \endcode
/// then
/// \code
///   getText(S1, Context) = "if (!x) return foo()"
///   getExtendedText(S1, tok::TokenKind::semi, Context)
///     = "if (!x) return foo();"
///   getExtendedText(*S1.getThen(), tok::TokenKind::semi, Context)
///     = "return foo();"
///   getExtendedText(*S2.getThen(), tok::TokenKind::semi, Context)
///     = getText(S2, Context) = "{ return 3; }"
/// \endcode
template <typename T>
StringRef getExtendedText(const T &Node, tok::TokenKind Next,
                          ASTContext &Context) {
  return internal::getText(getExtendedRange(Node, Next, Context), Context);
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

// Returns the start location of the first token starting before \p
// Start. Returns an invalid location if no previous token is found.
SourceLocation findPreviousTokenStart(SourceLocation Start,
                                      const SourceManager &SM,
                                      const LangOptions &LangOpts);

// Returns the start location of the first token of the given kind starting
// before \p Start. Returns an invalid location if none is found.
SourceLocation findPreviousTokenKind(SourceLocation Start,
                                     const SourceManager &SM,
                                     const LangOptions &LangOpts,
                                     tok::TokenKind TK);

// Returns the location of the open paren of the call expression, or an invalid
// location if no open paren is found.
SourceLocation findOpenParen(const CallExpr &E, const SourceManager &SM,
                             const LangOptions &LangOpts);

// Conservatively estimates whether the given expression should be wrapped in
// parentheses when printing (to avoid misinterpretation during parsing),
// assuming no other information about the surrounding context.
bool needsParens(const Expr &E);

// Formats a pointer to an expression: prefix with '*' but simplify when it
// already begins with '&'.  Return empty string on failure.
std::string formatDereference(const ASTContext &Context, const Expr &ExprNode);

// Formats a pointer to an expression: prefix with '&' but simplify when it
// already begins with '*'.  Returns empty string on failure.
std::string formatAddressOf(const ASTContext &Context, const Expr &Expr);

// Adds a dot to the end of the given expression, but adds parentheses when
// needed by the syntax, and simplifies to '->' when possible, e.g.:
//
//  x becomes x.
//  *a becomes a->
//  a+b becomes (a+b).
std::string formatDot(const ASTContext &Context, const Expr &Expr);

// Adds an arrow to the end of the given expression, but adds parentheses
// when needed by the syntax, and simplifies to '.' when possible, e.g.:
//
//  x becomes x->
//  &a becomes a.
//  a+b becomes (a+b)->
std::string formatArrow(const ASTContext &Context, const Expr &Expr);

} // end namespace fixit
} // end namespace tooling
} // end namespace clang

#endif // LLVM_CLANG_TOOLING_FIXINT_H
