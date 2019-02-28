//===--- NodeId.h - NodeId class ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLING_REFACTOR_NODE_ID_H_
#define LLVM_CLANG_TOOLING_REFACTOR_NODE_ID_H_

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "llvm/ADT/StringRef.h"
#include <string>

namespace clang {
namespace tooling {

/// A strong type for AST node identifiers.  The standard API uses StringRefs
/// for identifiers.  The strong type allows us to distinguish ids from
/// arbitrary text snippets in various parts of the API.
class NodeId {
public:
  explicit NodeId(std::string Id) : Id(std::move(Id)) {}

  /// Creates a NodeId whose name is based on \p Id. Guarantees that unique ids
  /// map to unique NodeIds.
  explicit NodeId(size_t Id) : Id("id" + std::to_string(Id)) {}

  /// Creates a NodeId with a generated name. The name is guaranteed to be unique
  /// with respect to other generated names.
  NodeId();

  llvm::StringRef id() const { return Id; }

  /// Gets the AST node in \p Result corresponding to this NodeId, if
  /// any. Otherwise, returns null.
  template <typename Node>
  const Node *
  getNodeAs(const ast_matchers::MatchFinder::MatchResult &Result) const {
    return Result.Nodes.getNodeAs<Node>(Id);
  }

private:
  std::string Id;
};

} // namespace tooling
} // namespace clang
#endif // LLVM_CLANG_TOOLING_REFACTOR_NODE_ID_H_
