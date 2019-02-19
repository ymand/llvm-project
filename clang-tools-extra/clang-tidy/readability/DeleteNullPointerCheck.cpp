//===--- DeleteNullPointerCheck.cpp - clang-tidy---------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "DeleteNullPointerCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"
#include "clang/Tooling/Refactoring/Transformer.h"

using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace readability {

tooling::RewriteRule RewriteDeleteNullPointer() {
  const auto DeleteExpr = cxxDeleteExpr(has(
      castExpr(has(declRefExpr(to(decl(equalsBoundNode("deletedPointer"))))))));

  const auto DeleteMemberExpr = cxxDeleteExpr(has(castExpr(has(memberExpr(
      hasDeclaration(fieldDecl(equalsBoundNode("deletedMemberPointer"))))))));

  const auto PointerExpr = ignoringImpCasts(anyOf(
      declRefExpr(to(decl().bind("deletedPointer"))),
      memberExpr(hasDeclaration(fieldDecl().bind("deletedMemberPointer")))));

  const auto PointerCondition = castExpr(hasCastKind(CK_PointerToBoolean),
                                         hasSourceExpression(PointerExpr));
  const auto BinaryPointerCheckCondition =
      binaryOperator(hasEitherOperand(castExpr(hasCastKind(CK_NullToPointer))),
                     hasEitherOperand(PointerExpr));

  tooling::StmtId DelStmt;
  using tooling::bind;
  using tooling::stencil_generators::statements;
  return tooling::RewriteRule()
      .matching(ifStmt(
          hasCondition(anyOf(PointerCondition, BinaryPointerCheckCondition)),
          hasThen(bind(
              DelStmt,
              stmt(anyOf(DeleteExpr, DeleteMemberExpr,
                         compoundStmt(statementCountIs(1),
                                      has(stmt(anyOf(DeleteExpr,
                                                     DeleteMemberExpr)))))))),
          // FIXME: handle else case.
          unless(hasElse(stmt()))))
      .replaceWith(statements(DelStmt))
      .explain(
          "'if' statement is unnecessary; deleting null pointer has no effect");
}

} // namespace readability
} // namespace tidy
} // namespace clang
