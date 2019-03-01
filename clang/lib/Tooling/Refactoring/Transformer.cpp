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
static CharSourceRange
getTarget(const clang::ast_type_traits::DynTypedNode &Node, NodePart TargetPart,
          ASTContext &Context) {
  SourceLocation TokenLoc;
  switch (TargetPart) {
  case NodePart::kNode:
    return fixit::getSourceRangeAuto(Node, Context);
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
// FIXME: take TextChange instead of a Rule.
Expected<TransformationGroup> transform(const MatchResult &Result,
                                        const RewriteRule &Rule) {
  TransformationGroup Group;

  // Ignore results in failing TUs or those rejected by the where clause.
  if (Result.Context->getDiagnostics().hasErrorOccurred() ||
      !Rule.filter().matches(Result)) {
    return Group;
  }

  // Get the root as anchor.
  auto &NodesMap = Result.Nodes.getMap();
  auto Root = NodesMap.find(RewriteRule::rootId());
  if (Root == NodesMap.end())
    return unboundNodeError("root id", RewriteRule::rootId());

  SourceLocation RootLoc = Root->second.getSourceRange().getBegin();
  if (RootLoc.isInvalid() ||
      isOriginMacroBody(*Result.SourceManager, RootLoc))
    return Group;
  Group.Anchor = RootLoc;

  for (const auto& Change : Rule.changes()) {
    auto It = NodesMap.find(Change.target());
    if (It == NodesMap.end()) {
      return unboundNodeError("Change.target()", Change.target());
    }
    if (auto Err = llvm::handleErrors(
            verifyTarget(It->second, Change.part()), [&Change](StringError &E) {
              return invalidArgumentError("Failure targeting node" +
                                          Change.target() + ": " +
                                          E.getMessage());
            })) {
      return std::move(Err);
    }
    CharSourceRange Target =
        getTarget(It->second, Change.part(), *Result.Context);
    if (Target.isInvalid() ||
        isOriginMacroBody(*Result.SourceManager, Target.getBegin())) {
      Group.Anchor = SourceLocation();
      return Group;
    }
    auto ReplacementOrErr = Change.replacement().eval(Result);
    if (auto Err = ReplacementOrErr.takeError())
      return std::move(Err);

    Group.Transformations.emplace_back(Target, std::move(*ReplacementOrErr));
  }

  return Group;
}
} // namespace internal

TextChange::TextChange(StringRef Target, NodePart Part)
    : Target(Target.str()), Part(Part) {}

TextChange &&TextChange::to(Stencil S) && {
  Replacement = std::move(S);
  return std::move(*this);
}

RewriteRule::RewriteRule() : Matcher(stmt()) {}

constexpr char RewriteRule::RootId[];

RewriteRule &
RewriteRule::where(std::function<bool(const MatchResult &Result)> FilterFn) & {
  Filter = MatchFilter(std::move(FilterFn));
  return *this;
}

RewriteRule &RewriteRule::addHeader(StringRef Header) & {
  AddedHeaders.push_back(Header.str());
  return *this;
}

RewriteRule &RewriteRule::removeHeader(StringRef Header) & {
  RemovedHeaders.push_back(Header.str());
  return *this;
}

RewriteRule &RewriteRule::change(TextChange Change) & {
  Changes.push_back(std::move(Change));
  return *this;
}

RewriteRule &RewriteRule::changes(std::vector<TextChange> CS) & {
  Changes = std::move(CS);
  return *this;
}

RewriteRule makeRule(StatementMatcher Matcher, Stencil Replacement,
                     std::string Explanation) {
  return RewriteRule()
      .matching(stmt(Matcher))
      .change(TextChange(RewriteRule::rootId())
                 .to(std::move(Replacement))
                 .because(std::move(Explanation)));
}

void Transformer::registerMatchers(MatchFinder *MatchFinder) {
  MatchFinder->addDynamicMatcher(Rule.matcher(), this);
}

void Transformer::run(const MatchResult &Result) {
  auto RewritesOrErr = internal::transform(Result, Rule);

  // Validate that result.
  if (auto Err = RewritesOrErr.takeError()) {
    llvm::errs() << "Rewrite failed: " << llvm::toString(std::move(Err))
                 << "\n";
    return;
  }
  auto &Rewrites = *RewritesOrErr;
  if (Rewrites.Anchor.isInvalid()) {
    // No rewrite applied (but no error encountered either).
    return;
  }

  // Convert the result to an AtomicChange.
  AtomicChange AC(*Result.SourceManager, Rewrites.Anchor);
  for (const auto &T : Rewrites.Transformations)
    if (auto Err = AC.replace(*Result.SourceManager, T.Range, T.Replacement)) {
      AC.setError(llvm::toString(std::move(Err)));
      break;
    }

  if (!AC.hasError()) {
    for (const auto &header : Rule.addedHeaders()) {
      AC.addHeader(header);
    }
    for (const auto &header : Rule.removedHeaders()) {
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
  if (Matches.empty())
    return llvm::None;

  if (Rule.changes().size() != 1)
    return invalidArgumentError("rule has multiple changes, which is not "
                                "allowed when transforming a single node");
  if (Rule.changes()[0].target() != RewriteRule::rootId() ||
      Rule.changes()[0].part() != NodePart::kNode)
    return invalidArgumentError("rule subselects on node, which is not allowed "
                                "when transforming a single node");
  if (Matches.size() > 1)
    return invalidArgumentError("rule is ambiguous");

  auto RewritesOrErr =
      internal::transform(MatchResult(Matches[0], Context), Rule);
  if (auto Err = RewritesOrErr.takeError()) {
    return std::move(Err);
  }
  auto &Rewrites = *RewritesOrErr;
  if (Rewrites.Anchor.isInvalid()) {
    return llvm::None;
  }
  assert(Rewrites.Transformations.size() == 1 &&
         "expected one transformation result to match the one requested");
  return Rewrites.Transformations[0].Replacement;
}
} // namespace tooling
} // namespace clang
