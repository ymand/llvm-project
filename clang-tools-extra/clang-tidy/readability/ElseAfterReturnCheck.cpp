//===--- ElseAfterReturnCheck.cpp - clang-tidy-----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "ElseAfterReturnCheck.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Tooling/FixIt.h"
#include "clang/Tooling/Refactoring/Transformer.h"

using namespace clang::ast_matchers;

namespace clang {
namespace tidy {
namespace readability {

static tooling::RewriteRule RewriteElse(
    ast_matchers::StatementMatcher InterruptsControlFlow,
    StringRef ControlFlowInterruptor) {
  using tooling::stencil_generators::statements;
  tooling::StmtId IfS("If"), CondS("C"), ThenS("T"), ElseS("E");
  return tooling::RewriteRule()
      .matching(compoundStmt(forEach(
          ifStmt(IfS.bind(), hasCondition(CondS.bind()), unless(isConstexpr()),
                 // FIXME: Explore alternatives for the
                 // `if (T x = ...) {... return; } else { <use x> }`
                 // pattern:
                 //   * warn, but don't fix;
                 //   * fix by pulling out the variable declaration out of
                 //     the condition.
                 unless(hasConditionVariableStatement(anything())),
                 hasThen(stmt(ThenS.bind(),
                              anyOf(InterruptsControlFlow,
                                    compoundStmt(has(InterruptsControlFlow))))),
                 hasElse(ElseS.bind())))))
      .change(IfS)
      .replaceWith("if (", CondS, ") ", ThenS, " ", statements(ElseS))
      .explain("do not use 'else' after '", ControlFlowInterruptor, "'");
}

std::vector<tooling::RewriteRule> RewriteElseAfterBranch() {
  return {RewriteElse(returnStmt(), "return"),
          RewriteElse(continueStmt(), "continue"),
          RewriteElse(breakStmt(), "break"),
          RewriteElse(expr(ignoringImplicit(cxxThrowExpr())), "throw")};
}

} // namespace readability
} // namespace tidy
} // namespace clang
