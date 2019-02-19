//===---------- TransformerTidy.cpp - clang-tidy -------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "TransformerTidy.h"

namespace clang {
namespace tidy {
namespace utils {

void TransformerTidy::registerMatchers(ast_matchers::MatchFinder *Finder) {
  Finder->addDynamicMatcher(Rule.matcher(), this);
}

void TransformerTidy::check(
    const ast_matchers::MatchFinder::MatchResult &Result) {
  auto ChangeOrErr = tooling::internal::transform(Result, Rule);
  if (auto Err = ChangeOrErr.takeError()) {
    llvm::errs() << "Rewrite failed: " << llvm::toString(std::move(Err))
                 << "\n";
    return;
  }
  auto &Change = *ChangeOrErr;
  auto &Range = Change.Range;
  if (Range.isInvalid()) {
    // No rewrite applied (but no error encountered either).
    return;
  }
  auto MessageOrErr = Rule.explanation().eval(Result);
  if (auto Err = MessageOrErr.takeError()) {
    llvm::errs() << "Evaluation of the explanation stencil failed: "
                 << llvm::toString(std::move(Err)) << "\n";
    return;
  }
  StringRef Message = *MessageOrErr;
  if (Message.empty()) {
    Message = "no explanation";
  }
  diag(Range.getBegin(), Message)
      << FixItHint::CreateReplacement(Range, Change.Replacement);
  // FIXME: Should we warn if added_headers/removed_headers is non empty?
}

MultiTransformerTidy::MultiTransformerTidy(
    std::vector<tooling::RewriteRule> Rules, StringRef Name,
    ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context) {
  for (auto &R : Rules) {
    Tidies.emplace_back(std::move(R), Name, Context);
  }
}

void MultiTransformerTidy::registerMatchers(ast_matchers::MatchFinder *Finder) {
  for (auto &T : Tidies) {
    T.registerMatchers(Finder);
  }
}

} // namespace utils
} // namespace tidy
} // namespace clang
