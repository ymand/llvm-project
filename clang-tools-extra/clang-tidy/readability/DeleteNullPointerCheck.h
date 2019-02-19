//===--- DeleteNullPointerCheck.h - clang-tidy-------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_READABILITY_DELETE_NULL_POINTER_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_READABILITY_DELETE_NULL_POINTER_H

#include "../ClangTidyCheck.h"
#include "../utils/TransformerTidy.h"

namespace clang {
namespace tidy {
namespace readability {

/// Check whether the 'if' statement is unnecessary before calling 'delete' on a
/// pointer.
///
/// For the user-facing documentation see:
/// http://clang.llvm.org/extra/clang-tidy/checks/readability-delete-null-pointer.html
tooling::RewriteRule RewriteDeleteNullPointer();

class DeleteNullPointerCheck : public utils::TransformerTidy {
public:
  DeleteNullPointerCheck(StringRef Name, ClangTidyContext *Context)
      : TransformerTidy(RewriteDeleteNullPointer(), Name, Context) {}
};

} // namespace readability
} // namespace tidy
} // namespace clang

#endif // LLVM_CLANG_TOOLS_EXTRA_CLANG_TIDY_READABILITY_DELETE_NULL_POINTER_H
