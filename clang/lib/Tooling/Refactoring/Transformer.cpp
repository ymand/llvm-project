//===--- Transformer.cpp - Transformer library implementation ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/Transformer.h"

#include <deque>
#include <string>
#include <utility>
#include <vector>

#include "clang/AST/Expr.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/FixIt.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Refactoring/AtomicChange.h"
#include "clang/Tooling/Refactoring/Stencil.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Errc.h"
#include "llvm/Support/Error.h"

namespace clang {
namespace tooling {
namespace {
using ::clang::ast_matchers::MatchFinder;
using ::clang::ast_matchers::stmt;
using ::llvm::Error;
using ::llvm::Expected;
using ::llvm::Optional;
using ::llvm::StringError;
using ::llvm::StringRef;

using MatchResult = MatchFinder::MatchResult;
} // namespace

static bool isOriginMacroBody(const clang::SourceManager &source_manager,
                              clang::SourceLocation loc) {
  while (loc.isMacroID()) {
    if (source_manager.isMacroBodyExpansion(loc))
      return true;
    // Otherwise, it must be in an argument, so we continue searching up the
    // invocation stack. getImmediateMacroCallerLoc() gives the location of the
    // argument text, inside the call text.
    loc = source_manager.getImmediateMacroCallerLoc(loc);
  }
  return false;
}

static llvm::Error invalidArgumentError(llvm::Twine Message) {
  return llvm::make_error<StringError>(llvm::errc::invalid_argument, Message);
}

static llvm::Error unboundNodeError(StringRef Role, StringRef Id) {
  return invalidArgumentError(Role + " (" + Id + ") references unbound node");
}

static llvm::Error typeError(llvm::Twine Message,
                             const clang::ast_type_traits::ASTNodeKind &Kind) {
  return invalidArgumentError(Message + " (node kind is " + Kind.asStringRef() +
                              ")");
}

static llvm::Error missingPropertyError(llvm::Twine Description,
                                        StringRef Property) {
  return invalidArgumentError(Description + " requires property '" + Property +
                              "'");
}

// Verifies that `node` is appropriate for the given `target_part`.
static Error verifyTarget(const clang::ast_type_traits::DynTypedNode &Node,
                          NodePart TargetPart) {
  switch (TargetPart) {
  case NodePart::kNode:
    return Error::success();
  case NodePart::kMember:
    if (Node.get<clang::MemberExpr>() != nullptr) {
      return Error::success();
    }
    return typeError("NodePart::kMember applied to non-MemberExpr",
                     Node.getNodeKind());
  case NodePart::kName:
    if (const auto *D = Node.get<clang::NamedDecl>()) {
      if (D->getDeclName().isIdentifier()) {
        return Error::success();
      }
      return missingPropertyError("NodePart::kName", "identifier");
    }
    if (const auto *E = Node.get<clang::DeclRefExpr>()) {
      if (E->getNameInfo().getName().isIdentifier()) {
        return Error::success();
      }
      return missingPropertyError("NodePart::kName", "identifier");
    }
    if (const auto *I = Node.get<clang::CXXCtorInitializer>()) {
      if (I->isMemberInitializer()) {
        return Error::success();
      }
      return missingPropertyError("NodePart::kName", "member initializer");
    }
    return typeError(
        "NodePart::kName applied to neither DeclRefExpr, NamedDecl nor "
        "CXXCtorInitializer",
        Node.getNodeKind());
  }
  llvm_unreachable("Unexpected case in NodePart type.");
}

// Requires VerifyTarget(node, target_part) == success.
static CharSourceRange getTarget(const clang::ast_type_traits::DynTypedNode &Node,
                             NodePart TargetPart, ASTContext &Context) {
  SourceLocation TokenLoc;
  switch (TargetPart) {
  case NodePart::kNode:
    return fixit::getSourceRangeSmart(Node, Context);
  case NodePart::kMember:
    TokenLoc = Node.get<clang::MemberExpr>()->getMemberLoc();
    break;
  case NodePart::kName:
    if (const auto *D = Node.get<clang::NamedDecl>()) {
      TokenLoc = D->getLocation();
      break;
    }
    if (const auto *E = Node.get<clang::DeclRefExpr>()) {
      TokenLoc = E->getLocation();
      break;
    }
    if (const auto *I = Node.get<clang::CXXCtorInitializer>()) {
      TokenLoc = I->getMemberLocation();
      break;
    }
    // This should be unreachable if the target was already verified.
    llvm_unreachable("NodePart::kName applied to neither NamedDecl nor "
                     "CXXCtorInitializer");
  }
  return CharSourceRange::getTokenRange(TokenLoc, TokenLoc);
}

namespace internal {
Expected<Transformation> transform(const MatchResult &Result,
                                   const RewriteRule &Rule) {
  // Ignore results in failing TUs or those rejected by the where clause.
  if (Result.Context->getDiagnostics().hasErrorOccurred() ||
      !Rule.filter().matches(Result)) {
    return Transformation();
  }

  auto &NodesMap = Result.Nodes.getMap();
  auto It = NodesMap.find(Rule.target());
  if (It == NodesMap.end()) {
    return unboundNodeError("rule.target()", Rule.target());
  }
  if (auto Err = llvm::handleErrors(
          verifyTarget(It->second, Rule.targetPart()), [&Rule](StringError &E) {
            return invalidArgumentError("Failure targeting node" +
                                        Rule.target() + ": " + E.getMessage());
          })) {
    return std::move(Err);
  }
  CharSourceRange Target =
      getTarget(It->second, Rule.targetPart(), *Result.Context);
  if (Target.isInvalid() ||
      isOriginMacroBody(*Result.SourceManager, Target.getBegin())) {
    return Transformation();
  }

  if (auto ReplacementOrErr = Rule.replacement().eval(Result)) {
    return Transformation{Target, std::move(*ReplacementOrErr)};
  } else {
    return ReplacementOrErr.takeError();
  }
}
} // namespace internal

RewriteRule::RewriteRule()
    : Matcher(stmt()), Target(RootId), TargetPart(NodePart::kNode) {}

constexpr char RewriteRule::RootId[];

RewriteRule &
RewriteRule::where(std::function<bool(const MatchResult &Result)> FilterFn) & {
  Filter = MatchFilter(std::move(FilterFn));
  return *this;
}

RewriteRule &RewriteRule::change(const NodeId &TargetId, NodePart Part) & {
  Target = std::string(TargetId.id());
  TargetPart = Part;
  return *this;
}

RewriteRule &RewriteRule::replaceWith(Stencil S) & {
  Replacement = std::move(S);
  return *this;
}

RewriteRule makeRule(StatementMatcher Matcher, Stencil Replacement,
                     std::string Explanation) {
  return RewriteRule()
      .matching(stmt(Matcher))
      .replaceWith(std::move(Replacement))
      .explain(std::move(Explanation));
}

void Transformer::registerMatchers(MatchFinder *MatchFinder) {
  MatchFinder->addDynamicMatcher(Rule.matcher(), this);
}

void Transformer::run(const MatchResult &Result) {
  auto ChangeOrErr = internal::transform(Result, Rule);
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
  AtomicChange AC(*Result.SourceManager, Range.getBegin());
  if (auto Err = AC.replace(*Result.SourceManager, Range, Change.Replacement)) {
    AC.setError(llvm::toString(std::move(Err)));
  } else {
    for (const auto &header : Rule.replacement().addedIncludes()) {
      AC.addHeader(header);
    }
    for (const auto &header : Rule.replacement().removedIncludes()) {
      AC.removeHeader(header);
    }
  }
  Consumer(AC);
}

MultiTransformer::MultiTransformer(std::vector<RewriteRule> Rules,
                                   const Transformer::ChangeConsumer &Consumer,
                                   MatchFinder *MF) {
  for (auto &R : Rules) {
    Transformers.emplace_back(std::move(R), Consumer);
    Transformers.back().registerMatchers(MF);
  }
}

static llvm::SmallVector<clang::ast_matchers::BoundNodes, 1>
match(const DynTypedMatcher &Matcher,
      const clang::ast_type_traits::DynTypedNode &Node,
      clang::ASTContext *Context) {
  clang::ast_matchers::internal::CollectMatchesCallback Callback;
  MatchFinder Finder;
  Finder.addDynamicMatcher(Matcher, &Callback);
  Finder.match(Node, *Context);
  return std::move(Callback.Nodes);
}

Expected<Optional<std::string>>
maybeTransform(const RewriteRule &Rule,
               const clang::ast_type_traits::DynTypedNode &Node,
               clang::ASTContext *Context) {
  auto Matches = match(Rule.matcher(), Node, Context);
  if (Matches.empty()) {
    return llvm::None;
  }
  if (Matches.size() > 1) {
    return invalidArgumentError("rule is ambiguous");
  }
  auto ChangeOrErr =
      internal::transform(MatchResult(Matches[0], Context), Rule);
  if (auto Err = ChangeOrErr.takeError()) {
    return std::move(Err);
  }
  auto &Change = *ChangeOrErr;
  if (Change.Range.isInvalid()) {
    return llvm::None;
  }
  return Change.Replacement;
}
} // namespace tooling
} // namespace clang
