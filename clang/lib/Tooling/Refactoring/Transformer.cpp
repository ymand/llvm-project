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

// @returns An invalid loc if \p Loc was sourced in a macro definition.
static SourceLocation getNonMacroBodyLoc(const SourceManager &SM,
                                         SourceLocation Loc) {
  // Search up the invocation stack until we find a location that is not the
  // expansion of a macro argument. getImmediateMacroCallerLoc() gives the
  // location of the argument text, inside the call text.
  while (SM.isMacroArgExpansion(Loc))
    Loc = SM.getImmediateMacroCallerLoc(Loc);
  return Loc.isMacroID() ? SourceLocation() : Loc;
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

// FIXME: Factor out code that operates on (Target, Part) pairs for unit
// testing.
//
// Verifies that `node` is appropriate for the given `target_part`.
static Error verifyTarget(const clang::ast_type_traits::DynTypedNode &Node,
                          NodePart TargetPart) {
  switch (TargetPart) {
  case NodePart::kNode:
  case NodePart::kExpansion:
  case NodePart::kBefore:
  case NodePart::kAfter:
    return Error::success();
  case NodePart::kMember:
    if (Node.get<clang::MemberExpr>() != nullptr) {
      return Error::success();
    }
    return typeError("NodePart::kMember applied to non-MemberExpr",
                     Node.getNodeKind());
  case NodePart::kName:
    if (Node.get<clang::FunctionDecl>() != nullptr) {
      // All functions have a name with a source range, even that name is not a
      // plain identifier.
      return Error::success();
    }
    if (const auto *D = Node.get<clang::NamedDecl>()) {
      // NamedDecl does not provide location info for its associated name
      // (unlike FunctionDecl), so we are limited to identifier names, which are
      // exactly one token and always begin at D->getLocation().
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
  case NodePart::kExpansion:
    return Context.getSourceManager().getExpansionRange(Node.getSourceRange());
  case NodePart::kBefore:
    return CharSourceRange::getCharRange(Node.getSourceRange().getBegin());
  case NodePart::kAfter:
    return CharSourceRange::getCharRange(Lexer::getLocForEndOfToken(
        Node.getSourceRange().getEnd(), 0, Context.getSourceManager(),
        Context.getLangOpts()));
  case NodePart::kMember:
    TokenLoc = Node.get<clang::MemberExpr>()->getMemberLoc();
    break;
  case NodePart::kName:
    if (const auto *FD = Node.get<clang::FunctionDecl>()) {
      return CharSourceRange::getTokenRange(FD->getNameInfo().getSourceRange());
    }
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

static CharSourceRange makeMacroFreeRange(CharSourceRange Range,
                                         const SourceManager &SM,
                                          const LangOptions &LangOpts) {
  // FIXME: We should checking that the whole range corresponds to one coherent
  // segment of non-macro code, which we can do with a check that the whole
  // range comes from the "expansion" of the same macro argument, as is done
  // here: clang/lib/Lex/Lexer.cpp:919.
  SourceLocation Begin = getNonMacroBodyLoc(SM, Range.getBegin());
  if (Begin.isInvalid())
    return {};
  SourceLocation End = getNonMacroBodyLoc(SM, Range.getEnd());
  if (End.isInvalid())
    return {};
  return Lexer::makeFileCharRange(
      CharSourceRange({Begin, End}, Range.isTokenRange()), SM, LangOpts);
}

namespace internal {
Expected<TransformationGroup> transform(const MatchResult &Result,
                                        llvm::ArrayRef<TextChange> Changes) {
  TransformationGroup Group;
  auto &NodesMap = Result.Nodes.getMap();
  for (const auto& Change : Changes) {
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
    CharSourceRange TargetRange = makeMacroFreeRange(
        getTarget(It->second, Change.part(), *Result.Context),
        *Result.SourceManager, Result.Context->getLangOpts());
    if (TargetRange.isInvalid())
      return TransformationGroup();
    auto ReplacementOrErr = Change.replacement(Result);
    if (auto Err = ReplacementOrErr.takeError())
      return std::move(Err);
    Group.emplace_back(TargetRange, std::move(*ReplacementOrErr));
  }

  return Group;
}
} // namespace internal

TextChange::TextChange(StringRef Target, NodePart Part)
    : Target(Target.str()), Part(Part) {}

void TextChange::setReplacement(TextGenerator T) {
  ReplacementGen = std::move(T);
}

TextChange &&TextChange::to(TextGenerator T) && {
  ReplacementGen = std::move(T);
  return std::move(*this);
}

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

RewriteRule &RewriteRule::apply(TextChange Change) & {
  Changes.push_back(std::move(Change));
  return *this;
}

RewriteRule &RewriteRule::applyAll(std::vector<TextChange> CS) & {
  Changes = std::move(CS);
  return *this;
}

RewriteRule makeRule(StatementMatcher Matcher, Stencil Replacement,
                     std::string Explanation) {
  return RewriteRule(Matcher).apply(TextChange(RewriteRule::matchedNode())
                                        .to(std::move(Replacement))
                                        .because(std::move(Explanation)));
}

///////////////

// Binds each rule's matcher to a unique (and deterministic) tag based on
// `TagBase`.
static std::vector<DynTypedMatcher>
taggedMatchers(StringRef TagBase, const std::vector<RewriteRule> &Rules) {
  std::vector<DynTypedMatcher> Matchers;
  Matchers.reserve(Rules.size());
  size_t count = 0;
  for (const auto &R : Rules) {
    std::string Tag = (TagBase + Twine(count)).str();
    ++count;
    auto M = R.matcher().tryBind(Tag);
    assert(M && "RewriteRule matchers should be bindable.");
    Matchers.push_back(*std::move(M));
  }
  return Matchers;
}

static bool isHigher(ast_type_traits::ASTNodeKind A,
                   ast_type_traits::ASTNodeKind B) {
  static auto QualKind =
      ast_type_traits::ASTNodeKind::getFromNodeKind<QualType>();
  static auto TypeKind = ast_type_traits::ASTNodeKind::getFromNodeKind<Type>();
  /// Mimic the implicit conversions of Matcher<>.
  /// - From Matcher<Type> to Matcher<QualType>
  /// - From Matcher<Base> to Matcher<Derived>
  return (A.isSame(TypeKind) && B.isSame(QualKind)) || A.isBaseOf(B);
}

// Try to find a common kind to which all of the rule's matchers can be
// converted.
static ast_type_traits::ASTNodeKind
findCommonKind(const std::vector<RewriteRule> &Rules) {
  assert(!Rules.empty());
  ast_type_traits::ASTNodeKind Join = Rules[0].matcher().getSupportedKind();
  // Find a (least) Kind K, for which M.canConvertTo(K) holds for all matchers
  // M in {Rule.matcher() | Rule in Rules}.
  for (const auto &R : Rules) {
    auto K = R.matcher().getSupportedKind();
    if (isHigher(Join, K)) {
      Join = K;
      continue;
    }
    if (K.isSame(Join) || isHigher(K, Join))
      // Join is already the lowest.
      continue;
    // K and Join are unrelated -- there is no least common kind.
    return ast_type_traits::ASTNodeKind();
  }
  return Join;
}

llvm::Optional<RewriteRuleSet>
RewriteRuleSet::constructForOp(DynTypedMatcher::VariadicOperator Op,
                               std::vector<RewriteRule> Rules) {
  auto CommonKind = findCommonKind(Rules);
  if (CommonKind.isNone())
    return llvm::None;
  // Explicitly bind `M` to ensure we use `Rules` before it is moved.
  auto M = DynTypedMatcher::constructVariadic(Op, CommonKind,
                                              taggedMatchers("Tag", Rules));
  return RewriteRuleSet(std::move(M), std::move(Rules));
}

const RewriteRule &
RewriteRuleSet::findSelectedRule(const MatchResult &Result) const {
  if (Rules.size() == 1) return Rules[0];

  auto &NodesMap = Result.Nodes.getMap();
  for (size_t i = 0, N = Rules.size(); i < N; ++i) {
    std::string Tag = ("Tag" + Twine(i)).str();
    if (NodesMap.find(Tag) != NodesMap.end())
      return Rules[i];
  }
  llvm_unreachable("No tag found for rule set.");
}
//////////////

void Transformer::registerMatchers(MatchFinder *MatchFinder) {
  MatchFinder->addDynamicMatcher(Rules.matcher(), this);
}

static bool isInsertion(const internal::Transformation& T) {
  return T.Range.isCharRange() && T.Range.getBegin() == T.Range.getEnd();
}

void Transformer::run(const MatchResult &Result) {
    // Ignore results in failing TUs.
  if (Result.Context->getDiagnostics().hasErrorOccurred())
    return;

  // Verify the existence and validity of the AST node that roots this change.
  auto &NodesMap = Result.Nodes.getMap();
  auto Root = NodesMap.find(RewriteRule::matchedNode());
  if (Root == NodesMap.end()) {
    llvm::errs() << "Rewrite failed: missing root node.\n";
    return;
  }

  const auto& Rule = Rules.findSelectedRule(Result);
    // Ignore results rejected by the where clause.
  if (!Rule.filter().matches(Result))
    return;
  auto RewritesOrErr = internal::transform(Result, Rule.changes());
  if (auto Err = RewritesOrErr.takeError()) {
    llvm::errs() << "Rewrite failed: " << llvm::toString(std::move(Err))
                 << "\n";
    return;
  }
  SourceLocation RootLoc = Result.SourceManager->getExpansionLoc(
      Root->second.getSourceRange().getBegin());
  auto &Rewrites = *RewritesOrErr;
  if (Rewrites.empty()) {
    // No rewrite applied (but no error encountered either).
    RootLoc.print(llvm::errs() << "note: skipping match at loc ",
                  *Result.SourceManager);
    llvm::errs() << "\n";
    return;
  }
  // Convert the result to an AtomicChange.
  if (RootLoc.isInvalid())
    return;
  AtomicChange AC(*Result.SourceManager, RootLoc);
  for (const auto &T : Rewrites)
    if (auto Err = isInsertion(T) ? AC.insert(*Result.SourceManager,
                                              T.Range.getBegin(), T.Replacement)
                                  : AC.replace(*Result.SourceManager, T.Range,
                                               T.Replacement)) {
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

static Expected<Optional<std::string>>
maybeTransformImpl(llvm::ArrayRef<TextChange> Changes,
                   const CharSourceRange &Range, StringRef Code,
                   const MatchResult &Result) {
  auto RewritesOrErr = internal::transform(Result, Changes);
  if (auto Err = RewritesOrErr.takeError())
    return std::move(Err);

  auto &Rewrites = *RewritesOrErr;
  if (Rewrites.empty())
    return llvm::None;

  const SourceLocation &Begin = Range.getBegin();
  const SourceLocation &End = Range.getEnd();

  SourceManager &SM = *Result.SourceManager;
  Replacements RS;
  for (const auto &T : Rewrites) {
    // All of the changes must occur within the range of the node.  We assume
    // that both ranges are well formed char ranges, with Begin <= End.
    if ((T.Range.getBegin() != Begin &&
         !SM.isBeforeInTranslationUnit(Begin, T.Range.getBegin())) ||
        (T.Range.getEnd() != End &&
         !SM.isBeforeInTranslationUnit(T.Range.getEnd(), End)))
      return invalidArgumentError("rule changes source outside of target node");

    if (auto Err = RS.add(Replacement(SM, T.Range, T.Replacement)))
      return std::move(Err);
  }

  auto NewCodeOrErr = applyAllReplacements(Code, RS);
  if (auto Err = NewCodeOrErr.takeError()) {
    return std::move(Err);
  }
  // FIXME: optimization: move this calculation to callers, since it is fixed
  // for a given Range.
  unsigned BeginOffset = SM.getDecomposedLoc(Range.getBegin()).second;
  // We need to shift the end point to account for changes, but the beginning
  // remains unchanged.
  unsigned EndOffset =
      RS.getShiftedCodePosition(SM.getDecomposedLoc(Range.getEnd()).second);
  return NewCodeOrErr->substr(BeginOffset, EndOffset - BeginOffset);
}

TextGenerator rewriteNode(std::string Node,
                          const std::vector<TextChange> &Changes) {
  return [=](const ast_matchers::MatchFinder::MatchResult &Result)
             -> Expected<std::string> {
    SourceManager &SM = *Result.SourceManager;

    auto &NodesMap = Result.Nodes.getMap();
    auto It = NodesMap.find(Node);
    if (It == NodesMap.end())
      return unboundNodeError("Node", Node);
    CharSourceRange Range = makeMacroFreeRange(
        CharSourceRange::getTokenRange(It->second.getSourceRange()), SM,
        Result.Context->getLangOpts());
    if (Range.isInvalid())
      return invalidArgumentError("Bad range for node");

    StringRef Code = SM.getBufferData(SM.getFileID(Range.getBegin()));
    auto TOrErr = maybeTransformImpl(Changes, Range, Code, Result);
    if (auto Err = TOrErr.takeError())
      return std::move(Err);
    auto &T = *TOrErr;
    if (!T)
      return invalidArgumentError("Code not eligible for replacement");
    return *T;
  };
}

Expected<llvm::SmallVector<std::string, 1>>
maybeTransform(const RewriteRule &Rule,
               const clang::ast_type_traits::DynTypedNode &Node,
               clang::ASTContext *Context) {
  llvm::SmallVector<std::string, 1> Outputs;

  SourceManager &SM = Context->getSourceManager();
  auto Range =
      makeMacroFreeRange(CharSourceRange::getTokenRange(Node.getSourceRange()),
                         SM, Context->getLangOpts());
  if (Range.isInvalid())
    return Outputs;
  StringRef Code = SM.getBufferData(SM.getFileID(Range.getBegin()));

  auto Matches = match(Rule.matcher(), Node, Context);
  for (const auto &Match : Matches) {
    MatchResult Result(Match, Context);
    // Ignore results rejected by the where clause.
    if (!Rule.filter().matches(Result))
      continue;
    auto TOrErr = maybeTransformImpl(Rule.changes(), Range, Code,
                                     Result);
    if (auto Err = TOrErr.takeError()) {
      return std::move(Err);
    }
    auto &T = *TOrErr;
    if (T)
      Outputs.push_back(std::move(*T));
  }
  return std::move(Outputs);
}
} // namespace tooling
} // namespace clang
