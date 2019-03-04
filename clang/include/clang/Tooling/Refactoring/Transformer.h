//===--- Transformer.h - Clang source-rewriting library ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
///  \file
///  Defines a library supporting the concise specification of clang-based
///  source-to-source transformations.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_TOOLING_REFACTOR_TRANSFORMER_H_
#define LLVM_CLANG_TOOLING_REFACTOR_TRANSFORMER_H_

#include "NodeId.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchersInternal.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/Error.h"
#include <deque>
#include <functional>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

namespace clang {
namespace tooling {

/// Derivation of NodeId that identifies the intended node type for the id,
/// which allows us to select appropriate overloads or constrain use of various
/// combinators. \p Node is the AST node type corresponding to this id.
template <typename Node> class TypedNodeId : public NodeId {
public:
  using NodeId::NodeId;
  using MatcherType = ast_matchers::internal::Matcher<Node>;

  /// Creates a matcher corresponding to the AST-node type of this id and bound
  /// to this id. Intended for settings where the type of matcher is
  /// obvious/uninteresting. For example,
  ///
  ///   ExprId Arg;
  ///   auto Matcher = callExpr(callee(isFunctionNamed("foo")),
  ///                           hasArgument(0, Arg.bind()));
  MatcherType bind() const {
    return ast_matchers::internal::BindableMatcher<Node>(
               ast_matchers::internal::TrueMatcher())
        .bind(id());
  }
};

using ExprId = TypedNodeId<Expr>;
using StmtId = TypedNodeId<Stmt>;
using DeclId = TypedNodeId<Decl>;
using TypeId = TypedNodeId<Type>;

/// Binds the node described by \p Matcher to the given \p Id.
template <typename T>
ast_matchers::internal::Matcher<T>
bind(const NodeId &Id, ast_matchers::internal::BindableMatcher<T> Matcher) {
  return Matcher.bind(Id.id());
}

/// \name Matcher-type abbreviations for all top-level classes in the
/// AST class hierarchy.
/// @{
using ast_matchers::CXXCtorInitializerMatcher;
using ast_matchers::DeclarationMatcher;
using ast_matchers::NestedNameSpecifierLocMatcher;
using ast_matchers::NestedNameSpecifierMatcher;
using ast_matchers::StatementMatcher;
using ast_matchers::TypeLocMatcher;
using ast_matchers::TypeMatcher;
using TemplateArgumentMatcher =
    ast_matchers::internal::Matcher<TemplateArgument>;
using TemplateNameMatcher = ast_matchers::internal::Matcher<TemplateName>;
using ast_matchers::internal::DynTypedMatcher;
/// @}

/// A simple abstraction of a filter for match results.  Currently, it simply
/// wraps a predicate, but we may extend the functionality to support a simple
/// boolean expression language for constructing filters.
class MatchFilter {
public:
  using Predicate =
      std::function<bool(const ast_matchers::MatchFinder::MatchResult &Result)>;

  MatchFilter()
      : Filter([](const ast_matchers::MatchFinder::MatchResult &) {
          return true;
        }) {}
  explicit MatchFilter(Predicate P) : Filter(std::move(P)) {}

  MatchFilter(const MatchFilter &) = default;
  MatchFilter(MatchFilter &&) = default;
  MatchFilter &operator=(const MatchFilter &) = default;
  MatchFilter &operator=(MatchFilter &&) = default;

  bool matches(const ast_matchers::MatchFinder::MatchResult &Result) const {
    return Filter(Result);
  }

private:
  Predicate Filter;
};

/// Determines the part of the AST node to replace.  We support this to work
/// around the fact that the AST does not differentiate various syntactic
/// elements into their own nodes, so users can specify them relative to a node,
/// instead.
enum class NodePart {
  /// The node itself.
  Node,
  /// Given a \c MemberExpr, selects the member's token.
  Member,
  /// Given a \c NamedDecl or \c CxxCtorInitializer, selects that token of the
  /// relevant name, not including qualifiers.
  Name,
};

using TextGenerator = std::function<llvm::Expected<std::string>(
    const ast_matchers::MatchFinder::MatchResult &)>;

/// Description of a source-code transformation.
//
// A *rewrite rule* describes a transformation of source code. It has the
// following components:
//
// * Matcher: the pattern term, expressed as clang matchers (with Transformer
//   extensions).
//
// * Where: a "where clause" -- that is, a predicate over (matched) AST nodes
//   that restricts matches beyond what is (easily) expressable as a pattern.
//
// * Target: the source code impacted by the rule. This identifies an AST node,
//   or part thereof, whose source range indicates the extent of the replacement
//   applied by the replacement term.  By default, the extent is the node
//   matched by the pattern term.
//
// * Replacement: the replacement function, which produces a replacement string
//   based on the match.
//
// * Explanation: explanation of the rewrite.
//
// Rules have an additional, implicit, component: the parameters. These are
// portions of the pattern which are left unspecified, yet named so that we can
// reference them in the replacement term.  The structure of parameters can be
// partially or even fully specified, in which case they serve just to identify
// matched nodes for later reference rather than abstract over portions of the
// AST.  However, in all cases, we refer to named portions of the pattern as
// parameters.
//
// Parameters can be declared explicitly using the NodeId type and its
// derivatives or left implicit by using the native support for binding ids in
// the clang matchers.
//
// RewriteRule is constructed in a "fluent" style, by chaining setters of
// individual components.  We provide ref-qualified overloads of the setters to
// avoid an unnecessary copy when a RewriteRule is initialized from a temporary,
// like:
// \code
//   RewriteRule R = RewriteRule().matching(functionDecl(...)).replaceWith(...);
// \endcode
class RewriteRule {
public:
  // `RewriteRule` supports all top-level nodes in the AST hierarchy.  We spell
  // out all of the permitted overloads, rather than defining a template, for
  // documentation purposes and to give the user clear error messages if they
  // pass a node that is not one of the permitted types.
  RewriteRule(CXXCtorInitializerMatcher M)
      : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(DeclarationMatcher M) : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(NestedNameSpecifierMatcher M)
      : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(NestedNameSpecifierLocMatcher M)
      : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(StatementMatcher M) : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(TemplateArgumentMatcher M) : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(TemplateNameMatcher M) : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(TypeLocMatcher M) : Matcher(makeMatcher(std::move(M))) {}
  RewriteRule(TypeMatcher M) : Matcher(makeMatcher(std::move(M))) {}

  RewriteRule(const RewriteRule &) = default;
  RewriteRule(RewriteRule &&) = default;
  RewriteRule &operator=(const RewriteRule &) = default;
  RewriteRule &operator=(RewriteRule &&) = default;

  RewriteRule &where(MatchFilter::Predicate Filter) &;
  RewriteRule &&where(MatchFilter::Predicate Filter) && {
    return std::move(where(std::move(Filter)));
  }

  RewriteRule &change(const NodeId &Target, NodePart Part = NodePart::Node) &;
  RewriteRule &&change(const NodeId &Target,
                       NodePart Part = NodePart::Node) && {
    return std::move(change(Target, Part));
  }

  RewriteRule &replaceWith(TextGenerator Replacement) &;
  RewriteRule &&replaceWith(TextGenerator Replacement) && {
    return std::move(replaceWith(std::move(Replacement)));
  }

  RewriteRule &because(TextGenerator Explanation) &;
  RewriteRule &&because(TextGenerator Explanation) && {
    return std::move(because(std::move(Explanation)));
  }

  const DynTypedMatcher &matcher() const { return Matcher; }
  const MatchFilter &filter() const { return Filter; }
  llvm::StringRef target() const { return Target; }
  NodePart targetPart() const { return TargetPart; }

  llvm::Expected<std::string>
  replacement(const ast_matchers::MatchFinder::MatchResult &R) const {
    return Replacement(R);
  }

  llvm::Expected<std::string>
  explanation(const ast_matchers::MatchFinder::MatchResult &R) const {
    return Explanation(R);
  }

private:
  template <typename MatcherT> static DynTypedMatcher makeMatcher(MatcherT M) {
    auto DM = DynTypedMatcher(M);
    DM.setAllowBind(true);
    // RewriteRule guarantees that the node described by the matcher will always
    // be accessible as `RootId`, so we bind it here. `tryBind` is guaranteed to
    // succeed, because `AllowBind` is true.
    auto Matcher = *DM.tryBind(RootId);
    // Allow clients of the rule to bind this matcher.
    Matcher.setAllowBind(true);
    return Matcher;
  }

  // Id used as the default target of each match.
  static constexpr char RootId[] = "___root___";

  // Supports any (top-level node) matcher type.
  DynTypedMatcher Matcher;
  MatchFilter Filter;
  // The (bound) id of the node whose source will be replaced.  This id should
  // never be the empty string. By default, refers to the node matched by
  // `Matcher`.
  std::string Target = RootId;
  NodePart TargetPart = NodePart::Node;
  TextGenerator Replacement;
  TextGenerator Explanation;
};

// Convenience factory function for the common case where a rule has a statement
// matcher, template and explanation.
RewriteRule makeRule(StatementMatcher Matcher, TextGenerator Replacement,
                     const std::string &Explanation);

// A class that handles the matcher and callback registration for a single
// rewrite rule, as defined by the arguments of the constructor.
class Transformer : public ast_matchers::MatchFinder::MatchCallback {
public:
  using ChangeConsumer =
      std::function<void(const clang::tooling::AtomicChange &Change)>;

  Transformer(RewriteRule Rule, ChangeConsumer Consumer)
      : Rule(std::move(Rule)), Consumer(std::move(Consumer)) {}

  // N.B. Passes `this` pointer to `MatchFinder`.  So, this object should not
  // be moved after this call.
  void registerMatchers(ast_matchers::MatchFinder *MatchFinder);

  // Not called directly by users -- called by the framework, via base class
  // pointer.
  void run(const ast_matchers::MatchFinder::MatchResult &Result) override;

private:
  RewriteRule Rule;
  ChangeConsumer Consumer;
};

namespace internal {
// A source "transformation," represented by a character range in the source to
// be replaced and a corresponding replacement string.
struct Transformation {
  CharSourceRange Range;
  std::string Replacement;
};

// Given a match and rule, tries to generate a transformation for the target of
// the rule. Fails if the match is not eligible for rewriting or any invariants
// are violated relating to bound nodes in the match.
Expected<Transformation>
transform(const ast_matchers::MatchFinder::MatchResult &Result,
          const RewriteRule &Rule);
} // namespace internal
} // namespace tooling
} // namespace clang

#endif // LLVM_CLANG_TOOLING_REFACTOR_TRANSFORMER_H_
