//===---------- TransformerTidy.h - clang-tidy ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_TRANSFORMER_TIDY_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_TRANSFORMER_TIDY_H

#include "../ClangTidy.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Tooling/Refactoring/Transformer.h"
#include <deque>
#include <vector>

namespace clang {
namespace tidy {
namespace utils {

// A ClangTidy encompassing a single rewrite rule.
class TransformerTidy : public ClangTidyCheck {
public:
  TransformerTidy(tooling::RewriteRule R, StringRef Name,
                  ClangTidyContext *Context)
      : ClangTidyCheck(Name, Context), Rule(std::move(R)) {}

  void registerMatchers(ast_matchers::MatchFinder *Finder) override;
  void check(const ast_matchers::MatchFinder::MatchResult &Result) override;

private:
  tooling::RewriteRule Rule;
};

class MultiTransformerTidy : public ClangTidyCheck {
public:
  MultiTransformerTidy(std::vector<tooling::RewriteRule> Rules, StringRef Name,
                       ClangTidyContext *Context);

  void registerMatchers(ast_matchers::MatchFinder *Finder) override;

  // `check` will never be called, since all of the matchers are registered to
  // child tidies.
  void check(const ast_matchers::MatchFinder::MatchResult &Result) override {}

private:
  // Use a deque to ensure pointer stability of elements.
  std::deque<TransformerTidy> Tidies;
};

} // namespace utils
} // namespace tidy
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_TRANSFORMER_TIDY_H
