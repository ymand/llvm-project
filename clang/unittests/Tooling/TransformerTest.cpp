//===- unittest/Tooling/TransformerTest.cpp -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/Transformer.h"

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Tooling/Tooling.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace clang {
namespace tooling {
namespace {
using ::clang::ast_matchers::anyOf;
using ::clang::ast_matchers::argumentCountIs;
using ::clang::ast_matchers::callee;
using ::clang::ast_matchers::callExpr;
using ::clang::ast_matchers::cxxMemberCallExpr;
using ::clang::ast_matchers::cxxMethodDecl;
using ::clang::ast_matchers::cxxRecordDecl;
using ::clang::ast_matchers::declRefExpr;
using ::clang::ast_matchers::expr;
using ::clang::ast_matchers::functionDecl;
using ::clang::ast_matchers::hasAnyName;
using ::clang::ast_matchers::hasArgument;
using ::clang::ast_matchers::hasDeclaration;
using ::clang::ast_matchers::hasElse;
using ::clang::ast_matchers::hasName;
using ::clang::ast_matchers::hasType;
using ::clang::ast_matchers::ifStmt;
using ::clang::ast_matchers::member;
using ::clang::ast_matchers::memberExpr;
using ::clang::ast_matchers::namedDecl;
using ::clang::ast_matchers::on;
using ::clang::ast_matchers::pointsTo;
using ::clang::ast_matchers::to;
using ::clang::ast_matchers::unless;

constexpr char KHeaderContents[] = R"cc(
  struct string {
    string(const char*);
    char* c_str();
    int size();
  };
  int strlen(const char*);

  namespace proto {
  struct PCFProto {
    int foo();
  };
  struct ProtoCommandLineFlag : PCFProto {
    PCFProto& GetProto();
  };
  }  // namespace proto
)cc";
} // namespace

static clang::ast_matchers::internal::Matcher<clang::QualType>
isOrPointsTo(const DeclarationMatcher &TypeMatcher) {
  return anyOf(hasDeclaration(TypeMatcher), pointsTo(TypeMatcher));
}

static std::string format(llvm::StringRef Code) {
  const std::vector<Range> Ranges(1, Range(0, Code.size()));
  auto Style = format::getLLVMStyle();
  const auto Replacements = format::reformat(Style, Code, Ranges);
  auto Formatted = applyAllReplacements(Code, Replacements);
  if (!Formatted) {
    ADD_FAILURE() << "Could not format code: "
                  << llvm::toString(Formatted.takeError());
    return std::string();
  }
  return *Formatted;
}

void compareSnippets(llvm::StringRef Expected,
                     const llvm::Optional<std::string> &MaybeActual) {
  ASSERT_TRUE(MaybeActual) << "Rewrite failed. Expecting: " << Expected;
  auto Actual = *MaybeActual;
  std::string HL = "#include \"header.h\"\n";
  auto I = Actual.find(HL);
  if (I != std::string::npos) {
    Actual.erase(I, HL.size());
  }
  EXPECT_EQ(format(Expected), format(Actual));
}

// FIXME: consider separating this class into its own file(s).
class ClangRefactoringTestBase : public testing::Test {
protected:
  void appendToHeader(llvm::StringRef S) { FileContents[0].second += S; }

  void addFile(llvm::StringRef Filename, llvm::StringRef Content) {
    FileContents.emplace_back(Filename, Content);
  }

  llvm::Optional<std::string> rewrite(llvm::StringRef Input) {
    std::string Code = ("#include \"header.h\"\n" + Input).str();
    auto Factory = newFrontendActionFactory(&MatchFinder);
    if (!runToolOnCodeWithArgs(
            Factory->create(), Code, std::vector<std::string>(), "input.cc",
            "clang-tool", std::make_shared<PCHContainerOperations>(),
            FileContents)) {
      return None;
    }
    auto ChangedCodeOrErr =
        applyAtomicChanges("input.cc", Code, Changes, ApplyChangesSpec());
    if (auto Err = ChangedCodeOrErr.takeError()) {
      llvm::errs() << "Change failed: " << llvm::toString(std::move(Err))
                   << "\n";
      return None;
    }
    return *ChangedCodeOrErr;
  }

  clang::ast_matchers::MatchFinder MatchFinder;
  AtomicChanges Changes;

private:
  FileContentMappings FileContents = {{"header.h", ""}};
};

class TransformerTest : public ClangRefactoringTestBase {
protected:
  TransformerTest() { appendToHeader(KHeaderContents); }

  Transformer::ChangeConsumer changeRecorder() {
    return [this](const AtomicChange &C) { Changes.push_back(C); };
  }
};

static TextGenerator text(const std::string &M) {
  return
      [M](const clang::ast_matchers::MatchFinder::MatchResult &) { return M; };
}

// Given string s, change strlen($s.c_str()) to $s.size()
RewriteRule ruleStrlenSize() {
  ExprId StringExpr;
  auto StringType = namedDecl(hasAnyName("::basic_string", "::string"));
  return makeRule(
      callExpr(callee(functionDecl(hasName("strlen"))),
               hasArgument(0, cxxMemberCallExpr(
                                  on(bind(StringExpr, expr(hasType(isOrPointsTo(
                                                          StringType))))),
                                  callee(cxxMethodDecl(hasName("c_str")))))),
      text("REPLACED"),
      "Use size() method directly on string.");
}

TEST_F(TransformerTest, StrlenSize) {
  std::string Input = "int f(string s) { return strlen(s.c_str()); }";
  std::string Expected = "int f(string s) { return REPLACED; }";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests that no change is applied when a match is not expected.
TEST_F(TransformerTest, NoMatch) {
  std::string Input = "int f(string s) { return s.size(); }";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // Input should not be changed.
  compareSnippets(Input, rewrite(Input));
}

// Tests that expressions in macro arguments are rewritten (when applicable).
TEST_F(TransformerTest, StrlenSizeMacro) {
  std::string Input = R"cc(
#define ID(e) e
    int f(string s) { return ID(strlen(s.c_str())); })cc";
  std::string Expected = R"cc(
#define ID(e) e
    int f(string s) { return ID(REPLACED); })cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Use the lvalue-ref overloads of the RewriteRule builder methods.
TEST_F(TransformerTest, LvalueRefOverloads) {
  StmtId E;
  RewriteRule Rule;
  Rule.matching(ifStmt(hasElse(E.bind())))
      .change(E)
      .replaceWith(text("bar();"));

  std::string Input = R"cc(
    void foo() {
      if (10 > 1.0)
        return;
      else
        foo();
    }
  )cc";
  std::string Expected = R"cc(
    void foo() {
      if (10 > 1.0)
        return;
      else
        bar();
    }
  )cc";

  Transformer T(Rule, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests replacing an expression.
TEST_F(TransformerTest, Flag) {
  ExprId Flag;
  auto Rule =
      RewriteRule()
          .matching(cxxMemberCallExpr(
              on(expr(Flag.bind(), hasType(cxxRecordDecl(hasName(
                                       "proto::ProtoCommandLineFlag"))))),
              unless(callee(cxxMethodDecl(hasName("GetProto"))))))
          .change(Flag)
          .replaceWith(text("EXPR"))
          .explain(text("Use GetProto() to access proto fields."));

  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
  )cc";
  std::string Expected = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = EXPR.foo();
    int y = flag.GetProto().foo();
  )cc";

  Transformer T(Rule, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, NodePartNameNamedDecl) {
  DeclId Fun;
  auto Rule = RewriteRule()
      .matching(functionDecl(hasName("bad"), Fun.bind()))
      .change(Fun, NodePart::kName)
      .replaceWith(text("good"));

  std::string Input = R"cc(
    int bad(int x);
    int bad(int x) { return x * x; }
  )cc";
  std::string Expected = R"cc(
    int good(int x);
    int good(int x) { return x * x; }
  )cc";

  Transformer T(Rule, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, NodePartNameDeclRef) {
  std::string Input = R"cc(
    template <typename T>
    T bad(T x) {
      return x;
    }
    int neutral(int x) { return bad<int>(x) * x; }
  )cc";
  std::string Expected = R"cc(
    template <typename T>
    T bad(T x) {
      return x;
    }
    int neutral(int x) { return good<int>(x) * x; }
  )cc";

  ExprId Ref;
  Transformer T(
      RewriteRule()
          .matching(declRefExpr(to(functionDecl(hasName("bad"))), Ref.bind()))
          .change(Ref, NodePart::kName)
          .replaceWith(text("good")),
      changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, NodePartNameDeclRefFailure) {
  std::string Input = R"cc(
    struct Y {};
    int operator*(const Y&);
    int neutral(int x) {
      Y y;
      return *y + x;
    }
  )cc";

  ExprId Ref;
  Transformer T(RewriteRule()
                    .matching(declRefExpr(to(functionDecl()), Ref.bind()))
                    .change(Ref, NodePart::kName)
                    .replaceWith(text("good")),
                changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Input, rewrite(Input));
}

TEST_F(TransformerTest, NodePartMember) {
  ExprId E;
  auto Rule = RewriteRule()
                  .matching(memberExpr(member(hasName("bad")), E.bind()))
                  .change(E, NodePart::kMember)
                  .replaceWith(text("good"));

  std::string Input = R"cc(
    struct S {
      int bad;
    };
    int g() {
      S s;
      return s.bad;
    }
  )cc";
  std::string Expected = R"cc(
    struct S {
      int bad;
    };
    int g() {
      S s;
      return s.good;
    }
  )cc";

  Transformer T(Rule, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// A rule that finds function calls with two arguments where the arguments are
// the same identifier.
RewriteRule ruleDuplicateArgs() {
  ExprId Arg0, Arg1;
  return RewriteRule()
      .matching(callExpr(argumentCountIs(2), hasArgument(0, Arg0.bind()),
                         hasArgument(1, Arg1.bind())))
      .where([Arg0, Arg1](
                 const clang::ast_matchers::MatchFinder::MatchResult &result) {
        auto *Ref0 = Arg0.getNodeAs<clang::DeclRefExpr>(result);
        auto *Ref1 = Arg1.getNodeAs<clang::DeclRefExpr>(result);
        return Ref0 != nullptr && Ref1 != nullptr &&
               Ref0->getDecl() == Ref1->getDecl();
      })
      .replaceWith(text("42"));
}

TEST_F(TransformerTest, FilterPassed) {
  std::string Input = R"cc(
    int foo(int x, int y);
    int x = 3;
    int z = foo(x, x);
  )cc";
  std::string Expected = R"cc(
    int foo(int x, int y);
    int x = 3;
    int z = 42;
  )cc";

  Transformer T(ruleDuplicateArgs(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

//
// Negative tests (where we expect no transformation to occur).
//

TEST_F(TransformerTest, FilterFailed) {
  std::string Input = R"cc(
    int foo(int x, int y);
    int x = 3;
    int y = 17;
    // Different identifiers.
    int z = foo(x, y);
    // One identifier, one not.
    int w = foo(x, 3);
  )cc";

  Transformer T(ruleDuplicateArgs(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Input, rewrite(Input));
}

TEST_F(TransformerTest, NoTransformationInMacro) {
  std::string Input = R"cc(
#define MACRO(str) strlen((str).c_str())
    int f(string s) { return MACRO(s); })cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
}

// This test handles the corner case where a macro called within another macro
// expands to matching code, but the matched code is an argument to the nested
// macro.  A simple check of isMacroArgExpansion() vs. isMacroBodyExpansion()
// will get this wrong, and transform the code. This test verifies that no such
// transformation occurs.
TEST_F(TransformerTest, NoTransformationInNestedMacro) {
  std::string Input = R"cc(
#define NESTED(e) e
#define MACRO(str) NESTED(strlen((str).c_str()))
    int f(string s) { return MACRO(s); })cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
}
} // namespace tooling
} // namespace clang
