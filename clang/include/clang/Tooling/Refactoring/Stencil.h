//===--- Stencil.h - Stencil class ------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file defines the *Stencil* abstraction: a code-generating object,
//  parameterized by named references to (bound) AST nodes.  Given a match
//  result, a stencil can be evaluated to a string of source code.
//
//  A stencil is similar in spirit to a format string: it is composed of a
//  series of raw text strings, references to nodes (the parameters) and helper
//  code-generation operations.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLING_REFACTOR_STENCIL_H_
#define LLVM_CLANG_TOOLING_REFACTOR_STENCIL_H_

#include <string>
#include <vector>

#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTTypeTraits.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace tooling {

// A strong type for AST node identifiers.  The standard API uses StringRefs for
// identifiers.  The strong type allows us to distinguish ids from arbitrary
// text snippets in various parts of the API.
class NodeId {
public:
  explicit NodeId(std::string Id) : Id(std::move(Id)) {}

  // Creates a NodeId whose name is based on the id. Guarantees that unique ids
  // map to unique NodeIds.
  explicit NodeId(size_t Id) : Id("id" + std::to_string(Id)) {}

  // Convenience constructor that generates a fresh id (with respect to other
  // generated ids).
  NodeId();

  llvm::StringRef id() const { return Id; }

  // Gets the AST node in `result` corresponding to this NodeId, if
  // any. Otherwise, returns null.
  template <typename Node>
  const Node *
  getNodeAs(const ast_matchers::MatchFinder::MatchResult &Result) const {
    return Result.Nodes.getNodeAs<Node>(Id);
  }

private:
  std::string Id;
};

// A stencil is represented as a sequence of "parts" that can each individually
// generate a code string based on a match result.  The different kinds of parts
// include (raw) text, references to bound nodes and assorted operations on
// bound nodes.
//
// Users can create custom Stencil operations by implementing this interface.
class StencilPartInterface {
public:
  StencilPartInterface() = default;
  virtual ~StencilPartInterface() = default;

  // Evaluates this part to a string and appends it to `result`.
  virtual llvm::Error eval(const ast_matchers::MatchFinder::MatchResult &Match,
                           std::string *Result) const = 0;

  virtual std::unique_ptr<StencilPartInterface> clone() const = 0;

protected:
  // Since this is an abstract class, copying/assigning only make sense for
  // derived classes implementing `Clone()`.
  StencilPartInterface(const StencilPartInterface &) = default;
  StencilPartInterface &operator=(const StencilPartInterface &) = default;
};

// A copyable facade for a std::unique_ptr<StencilPartInterface>. Copies result
// in a copy of the underlying pointee object.
class StencilPart {
public:
  explicit StencilPart(std::unique_ptr<StencilPartInterface> Impl)
      : Impl(std::move(Impl)) {}

  // Copy constructor/assignment produce a deep copy.
  StencilPart(const StencilPart &P) : Impl(P.Impl->clone()) {}
  StencilPart(StencilPart &&) = default;
  StencilPart &operator=(const StencilPart &P) {
    Impl = P.Impl->clone();
    return *this;
  }
  StencilPart &operator=(StencilPart &&) = default;

  // See StencilPartInterface::Eval.
  llvm::Error eval(const ast_matchers::MatchFinder::MatchResult &Match,
                   std::string *Result) const {
    return Impl->eval(Match, Result);
  }

private:
  std::unique_ptr<StencilPartInterface> Impl;
};

// Include directive modification
//
// Stencils also support operations to add and remove preprocessor include
// directives. Users specify the included file with a string, which can
// optionally be enclosed in <> or "". If unenclosed, surrounding double quotes
// are implied. The resulting string is treated literally in the relevant
// operation. No attempt is made to interpret the path in the string; for
// example, to identify it with another path that resolves to the same file.

// Add an #include for the specified path to the file being rewritten. No-op
// if the directive is already present. A `path` surrounded by <> adds a
// directive that uses <>; surrounded by "" (explicit or implicit) adds a
// directive that uses "".
struct AddIncludeOp {
  std::string Path;
};

// Remove an #include of the specified path from the file being rewritten.
// No-op if the include isn't present.  A `path` surrounded by <> removes a
// directive that uses <>; surrounded by "" (explicit or implicit) removes a
// directive that uses "".
struct RemoveIncludeOp {
  std::string Path;
};

// A sequence of code fragments, references to parameters and code-generation
// operations that together can be evaluated to (a fragment of) source code,
// given a match result.
class Stencil {
public:
  Stencil() = default;

  Stencil(const Stencil &) = default;
  Stencil(Stencil &&) = default;
  Stencil &operator=(const Stencil &) = default;
  Stencil &operator=(Stencil &&) = default;

  // Compose a stencil from a series of parts.
  template <typename... Ts> static Stencil cat(Ts &&... Parts) {
    Stencil Stencil;
    Stencil.Parts.reserve(sizeof...(Parts));
    auto Unused = {(Stencil.append(std::forward<Ts>(Parts)), true)...};
    (void)Unused;
    return Stencil;
  }

  // Evaluates the stencil given a match result. Requires that the nodes in the
  // result includes any ids referenced in the stencil. References to missing
  // nodes will result in an invalid_argument error.
  llvm::Expected<std::string>
  eval(const ast_matchers::MatchFinder::MatchResult &Match) const;

  // List of paths for which an include directive should be added. See
  // AddIncludeOp for the meaning of the path strings.
  const std::vector<std::string> &addedIncludes() const {
    return AddedIncludes;
  }

  // List of paths for which an include directive should be removed. See
  // RemoveIncludeOp for the meaning of the path strings.
  const std::vector<std::string> &removedIncludes() const {
    return RemovedIncludes;
  }

private:
  void append(const NodeId &Id);
  void append(llvm::StringRef Text);
  void append(StencilPart Part) { Parts.push_back(std::move(Part)); }
  void append(AddIncludeOp Op) { AddedIncludes.push_back(std::move(Op.Path)); }
  void append(RemoveIncludeOp Op) {
    RemovedIncludes.push_back(std::move(Op.Path));
  }

  std::vector<StencilPart> Parts;
  // See corresponding accessors for descriptions of these two fields.
  std::vector<std::string> AddedIncludes;
  std::vector<std::string> RemovedIncludes;
};

// Functions for conveniently building stencil parts.
namespace stencil_generators {
// Abbreviation for NodeId construction allowing for more concise references to
// node ids in stencils.
inline NodeId id(llvm::StringRef Id) { return NodeId(Id); }

// Yields exactly the text provided.
StencilPart text(llvm::StringRef Text);

// Yields the source corresponding to the identified node.
StencilPart node(const NodeId &Id);
StencilPart node(llvm::StringRef Id);

// Given a reference to a node e and a member m, yields "e->m", when e is a
// pointer, "e2->m" when e = "*e2" and "e.m" otherwise.  "e" is wrapped in
// parentheses, if needed.  Objects can be identified by NodeIds or strings and
// members can be identified by other parts (e.g. Name()) or raw text, hence the
// 4 overloads.
StencilPart member(const NodeId &ObjectId, StencilPart Member);
StencilPart member(const NodeId &ObjectId, llvm::StringRef Member);
StencilPart member(llvm::StringRef ObjectId, StencilPart Member);
StencilPart member(llvm::StringRef ObjectId, llvm::StringRef Member);

// Renders a node's source as a value, even if the node is a pointer.
// Specifically, given a reference to a node "e",
// * when "e" has the form `&$expr`, yields `$expr`.
// * when "e" is a pointer, yields `*$e`.
// * otherwise, yields `$e`.
StencilPart asValue(const NodeId &Id);
StencilPart asValue(llvm::StringRef Id);

// Renders a node's source as an address, even if the node is an lvalue.
// Specifically, given a reference to a node "e",
// * when "e" has the form `*$expr` (with '*' the builtin operator and `$expr`
//   source code of an arbitrary expression), yields `$expr`.
// * when "e" is a pointer, yields `$e`,
// * otherwise, yields `&$e`.
StencilPart asAddress(const NodeId &Id);
StencilPart asAddress(llvm::StringRef Id);

// Given a reference to a node "e", yields `($e)` if "e" may parse differently
// depending on context. For example, a binary operation is always wrapped while
// a variable reference is never wrapped.
StencilPart parens(const NodeId &Id);
StencilPart parens(llvm::StringRef Id);

// Given a reference to a named declaration "d" (that is, a node of type
// NamedDecl or one its derived classes), yields the name. "d" must have
// an identifier name (that is, constructors are not valid arguments to the Name
// operation).
StencilPart name(const NodeId &DeclId);
StencilPart name(llvm::StringRef DeclId);

// Given a reference to call expression node, yields the source text of the
// arguments (all source between the call's parentheses).
StencilPart args(const NodeId &CallId);
StencilPart args(llvm::StringRef CallId);

// Given a reference to a compound statement node, yields the source text of the
// statements (all source between the braces). If the statement is not compound,
// yields the statement's source text.
StencilPart statements(const NodeId &StmtId);
StencilPart statements(llvm::StringRef StmtId);

// Derive a string from a node.
using NodeFunction = std::function<std::string(
    const ast_type_traits::DynTypedNode &Node, const ASTContext &Context)>;

// Derive a string from the result of a stencil-part evaluation.
using StringFunction = std::function<std::string(llvm::StringRef)>;

// Yields the string from applying `fn` to the referenced node.
StencilPart apply(NodeFunction Fn, const NodeId &Id);
StencilPart apply(NodeFunction Fn, llvm::StringRef Id);

// Yields the string from applying `fn` to the evaluation of `part`.
StencilPart apply(StringFunction Fn, StencilPart Part);

// Convenience overloads for case where target part is a node.
StencilPart apply(StringFunction Fn, const NodeId &Id);
StencilPart apply(StringFunction Fn, llvm::StringRef Id);

// Add an include directive for 'path' into the file that is being rewritten.
// See comments on AddIncludeOp for more details. Not (yet) supported by clang
// tidy.
AddIncludeOp addInclude(llvm::StringRef Path);
// Remove an include directive for 'path' in the file that is being rewritten.
// See comments on RemoveIncludeOp for more details. Not (yet) supported by
// clang tidy.
RemoveIncludeOp removeInclude(llvm::StringRef Path);

// For debug use only; semantics are not guaranteed. Generates the string
// resulting from calling the node's print() method.
StencilPart dPrint(const NodeId &Id);
StencilPart dPrint(llvm::StringRef Id);
} // namespace stencil_generators
} // namespace tooling
} // namespace clang
#endif // LLVM_CLANG_TOOLING_REFACTOR_STENCIL_H_
