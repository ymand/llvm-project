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

// Determines whether `S` is a strictly a statement. Clang's class hierchy
// implicitly categorizes all expressions as statements. This function
// distinguishs expressions that appear in a context for which they are
// first-class statements.  In essence, this excludes expressions that are
// either part of another expression, the condition of a statement or a
// for-loop's init or increment.
static bool isStrictStatement(const Stmt &S, ASTContext &Context) {
  using namespace ast_matchers;

  if (!isa<Expr>(S))
    return true;

  auto NotCondition = unless(hasCondition(equalsNode(&S)));
  auto Standalone =
      stmt(hasParent(stmt(anyOf(compoundStmt(), ifStmt(NotCondition),
                                whileStmt(NotCondition), doStmt(NotCondition),
                                switchStmt(NotCondition), switchCase(),
                                forStmt(unless(hasLoopInit(equalsNode(&S))),
                                        unless(hasCondition(equalsNode(&S))),
                                        unless(hasIncrement(equalsNode(&S)))),
                                labelStmt()))))
          .bind("stmt");
  return !match(Standalone, S, Context).empty();
}

CharSourceRange getSourceRangeAuto(const Stmt &S, ASTContext &Context) {
  // Only exlude non-statement expressions.
  if (!isa<Expr>(S) || isStrictStatement(S, Context)) {
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
