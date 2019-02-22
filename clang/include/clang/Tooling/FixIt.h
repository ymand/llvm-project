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
StringRef getText(CharSourceRange Range, const ASTContext &Context);

/// Returns the SourceRange of a SourceRange. This identity function is
///        used by the following template abstractions.
inline CharSourceRange getSourceRange(const SourceRange &Range) {
  return CharSourceRange::getTokenRange(Range);
}

/// Returns the SourceRange of the token at Location \p Loc.
inline CharSourceRange getSourceRange(const SourceLocation &Loc) {
  return CharSourceRange::getTokenRange(Loc, Loc);
}

/// Returns the SourceRange of an given Node. \p Node is typically a
///        'Stmt', 'Expr' or a 'Decl'.
template <typename T> CharSourceRange getSourceRange(const T &Node) {
  return CharSourceRange::getTokenRange(Node.getSourceRange());
}
} // end namespace internal

// Returns a textual representation of \p Node.
template <typename T>
StringRef getText(const T &Node, const ASTContext &Context) {
  return internal::getText(internal::getSourceRange(Node), Context);
}

// Returns the source range spanning the statement and any trailing semicolon
// that belongs with that statement.
//
// N.B. The API of this function is still evolving and might change in the
// future to include more associated text (like comments).
CharSourceRange getSourceRangeAuto(const Stmt &S, ASTContext &Context);

CharSourceRange getSourceRangeAuto(const ast_type_traits::DynTypedNode &Node,
                                   ASTContext &Context);
// Catch all for any nodes that aren't DynTypedNode or derived from Stmt.
template <typename T, typename = typename std::enable_if<
                          (!std::is_base_of<Stmt, T>::value)>::type>
CharSourceRange getSourceRangeAuto(const T &Node, ASTContext &Context) {
  return internal::getSourceRange(Node);
}

// Gets the source text of the node, taking into account the node's type and
// context. In contrast with \p getText(), this function selects a source range
// "automatically", extracting text that a reader might intuitively associate
// with a node.  Currently, only specialized for \p clang::Stmt, where it will
// include any associated trailing semicolon.
template <typename T>
StringRef getTextAuto(const T &Node, ASTContext &Context) {
  return internal::getText(getSourceRangeAuto(Node, Context), Context);
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

} // end namespace fixit
} // end namespace tooling
} // end namespace clang

#endif // LLVM_CLANG_TOOLING_FIXINT_H
