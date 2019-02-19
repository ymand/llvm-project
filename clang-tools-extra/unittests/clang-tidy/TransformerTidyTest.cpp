//===---- TransformerTidyTest.cpp - clang-tidy ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "../clang-tidy/utils/TransformerTidy.h"

#include "ClangTidyTest.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "gtest/gtest.h"

namespace clang {
namespace tidy {
namespace utils {
namespace {
// Change `if ($c) $t $e` to `if (!$c) $e $t`.
//
// N.B. This rule is oversimplified (since it is just for testing): it won't
// construct the correct result if the input has compound statements.
tooling::RewriteRule invertIf() {
  using ast_matchers::hasCondition;
  using ast_matchers::hasElse;
  using ast_matchers::hasThen;
  using ast_matchers::ifStmt;

  tooling::ExprId C;
  tooling::StmtId T, E;

  return tooling::RewriteRule()
      .matching(
          ifStmt(hasCondition(C.bind()), hasThen(T.bind()), hasElse(E.bind())))
      .replaceWith("if(!(", C, ")) ", E, " else ", T);
}

class IfInverterTidy : public TransformerTidy {
 public:
  IfInverterTidy(StringRef Name, ClangTidyContext* Context)
      : TransformerTidy(invertIf(), Name, Context) {}
};

// Basic test of using a rewrite rule as a ClangTidy.
TEST(TransformerTidyTest, Basic) {
  const std::string Input = R"cc(
    void log(const char* msg);
    void foo() {
      if (10 > 1.0)
        log("oh no!");
      else
        log("ok");
    }
  )cc";

  const std::string Expected = R"(
    void log(const char* msg);
    void foo() {
      if(!(10 > 1.0)) log("ok"); else log("oh no!");
    }
  )";

  EXPECT_EQ(Expected, test::runCheckOnCode<IfInverterTidy>(Input));
}
}  // namespace
}  // namespace utils
}  // namespace tidy
}  // namespace clang
