//===- unittest/Tooling/TransformerTest.cpp -------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/Transformer.h"

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Tooling/Refactoring/Stencil.h"
#include "clang/Tooling/Tooling.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

#include "clang/ASTMatchers/ASTMatchersMacros.h"

namespace clang {
namespace tooling {
namespace {
using ::clang::ast_matchers::anyOf;
using ::clang::ast_matchers::argumentCountIs;
using ::clang::ast_matchers::callee;
using ::clang::ast_matchers::callExpr;
using ::clang::ast_matchers::cxxMemberCallExpr;
using ::clang::ast_matchers::cxxMethodDecl;
using ::clang::ast_matchers::cxxOperatorCallExpr;
using ::clang::ast_matchers::cxxRecordDecl;
using ::clang::ast_matchers::declRefExpr;
using ::clang::ast_matchers::eachOf;
using ::clang::ast_matchers::expr;
using ::clang::ast_matchers::functionDecl;
using ::clang::ast_matchers::has;
using ::clang::ast_matchers::hasAnyName;
using ::clang::ast_matchers::hasArgument;
using ::clang::ast_matchers::hasCondition;
using ::clang::ast_matchers::hasDeclaration;
using ::clang::ast_matchers::hasElse;
using ::clang::ast_matchers::hasName;
using ::clang::ast_matchers::hasOverloadedOperatorName;
using ::clang::ast_matchers::hasReturnValue;
using ::clang::ast_matchers::hasThen;
using ::clang::ast_matchers::hasType;
using ::clang::ast_matchers::id;
using ::clang::ast_matchers::ifStmt;
using ::clang::ast_matchers::ignoringImplicit;
using ::clang::ast_matchers::member;
using ::clang::ast_matchers::memberExpr;
using ::clang::ast_matchers::namedDecl;
using ::clang::ast_matchers::on;
using ::clang::ast_matchers::pointsTo;
using ::clang::ast_matchers::returnStmt;
using ::clang::ast_matchers::stmt;
using ::clang::ast_matchers::to;
using ::clang::ast_matchers::unless;

using stencil_generators::addInclude;
using stencil_generators::id;
using stencil_generators::member;
using stencil_generators::name;
using stencil_generators::parens;
using stencil_generators::removeInclude;

using ::testing::ElementsAre;

constexpr char KHeaderContents[] = R"cc(
  struct string {
    string(const char*);
    char* c_str();
    int size();
  };
  int strlen(const char*);

  class Logger {};
  void operator<<(Logger& l, string msg);
  Logger& log(int level);

  namespace proto {
  struct PCFProto {
    int foo();
  };
  struct ProtoCommandLineFlag : PCFProto {
    PCFProto& GetProto();
  };
  }  // namespace proto

  class Base {
   public:
    Base();
    virtual ~Base();

    virtual int Foo() = 0;
    virtual int Bar(int x) = 0;
  };
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

// TODO(yitzhakm): consider separating this class into its own file(s).
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

static TextChange changeAll() { return TextChange(RewriteRule::matchedNode()); }

// Change strlen($s.c_str()) to $s.size().
RewriteRule ruleStrlenSizeAny() {
  ExprId S;
  return RewriteRule(
             callExpr(
                 callee(functionDecl(hasName("strlen"))),
                 hasArgument(0, cxxMemberCallExpr(
                                    on(S.bind()),
                                    callee(cxxMethodDecl(hasName("c_str")))))))
      .apply(changeAll()
                 .to(Stencil::cat(S, ".size()"))
                 .because("Call size() method directly on object '", S, "'"));
}

// Tests that code that looks the same not involving the canonical string type
// is still transformed.
TEST_F(TransformerTest, OtherStringTypeWithAny) {
  std::string Input =
      R"cc(namespace foo {
           struct mystring {
             char* c_str();
           };
           int f(mystring s) { return strlen(s.c_str()); }
           }  // namespace foo)cc";
  std::string Expected =
      R"cc(namespace foo {
           struct mystring {
             char* c_str();
           };
           int f(mystring s) { return s.size(); }
           }  // namespace foo)cc";

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests makeRule.
RewriteRule ruleStrlenSize() {
  ExprId StringExpr;
  auto StringType = namedDecl(hasAnyName("::basic_string", "::string"));
  return makeRule(
      callExpr(callee(functionDecl(hasName("strlen"))),
               hasArgument(0, cxxMemberCallExpr(
                                  on(bind(StringExpr, expr(hasType(isOrPointsTo(
                                                          StringType))))),
                                  callee(cxxMethodDecl(hasName("c_str")))))),
      Stencil::cat(member(StringExpr, "size()")),
      "Use size() method directly on string.");
}

TEST_F(TransformerTest, StrlenSize) {
  std::string Input = "int f(string s) { return strlen(s.c_str()); }";
  std::string Expected = "int f(string s) { return s.size(); }";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests that expressions in macro arguments are rewritten (when applicable),
// for the case where the argument is part of the expansion.
TEST_F(TransformerTest, StrlenSizeMacro) {
  std::string Input = R"cc(
#define ID(e) 1 + e
    int f(string s) { return ID(strlen(s.c_str())); })cc";
  std::string Expected = R"cc(
#define ID(e) 1 + e
    int f(string s) { return ID(s.size()); })cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests that expressions in macro arguments are rewritten (when applicable),
// for the (rare) case where the argument is the entirety of the expansion.
TEST_F(TransformerTest, StrlenSizeMacroFull) {
  std::string Input = R"cc(
#define ID(e) e
    int f(string s) { return ID(strlen(s.c_str())); })cc";
  std::string Expected = R"cc(
#define ID(e) e
    int f(string s) { return ID(s.size()); })cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

RewriteRule ruleRenameFunctionAddHeader() {
  ExprId Arg;
  return RewriteRule(callExpr(callee(functionDecl(hasName("update"))),
                              hasArgument(0, Arg.bind())))
      .addHeader("foo/updater.h")
      .apply(changeAll().to(Stencil::cat("updateAddress(", Arg, ")")));
}

RewriteRule ruleRenameFunctionRemoveHeader() {
  ExprId Arg;
  return RewriteRule(callExpr(callee(functionDecl(hasName("updateAddress"))),
                         hasArgument(0, Arg.bind())))
      .removeHeader("foo/updater.h")
      .apply(changeAll().to(Stencil::cat("update(", Arg, ")")));
}

RewriteRule ruleRenameFunctionChangeHeader() {
  ExprId Arg;
  return RewriteRule(callExpr(callee(functionDecl(hasName("update"))),
                         hasArgument(0, Arg.bind())))
      .removeHeader("bar/updater.h")
      .addHeader("foo/updater.h")
      .apply(changeAll().to(Stencil::cat("updateAddress(", Arg, ")")));
}

TEST_F(TransformerTest, AddHeader) {
  std::string Input = R"cc(
    int update(int *i);
    int f(int i) { return update(&i); })cc";
  std::string Expected =
      R"cc(#include "foo/updater.h"

           int update(int *i);
           int f(int i) { return updateAddress(&i); })cc";

  Transformer T(ruleRenameFunctionAddHeader(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, RemoveHeader) {
  addFile("foo/updater.h", "int updateAddress(int *i);");
  std::string Input =
      R"cc(#include "foo/updater.h"

           int update(int *i);
           int f(int i) { return updateAddress(&i); })cc";
  std::string Expected = R"cc(
    int update(int *i);
    int f(int i) { return update(&i); })cc";

  Transformer T(ruleRenameFunctionRemoveHeader(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, ChangeHeader) {
  addFile("bar/updater.h", "int update(int *i);");
  std::string Input =
      R"cc(#include "bar/updater.h"
           int f(int i) { return update(&i); })cc";
  std::string Expected =
      R"cc(#include "foo/updater.h"
           int f(int i) { return updateAddress(&i); })cc";

  Transformer T(ruleRenameFunctionChangeHeader(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Change `if ($c) $t $e` to `if (!$c) $e $t`.
//
// N.B. This rule is oversimplified (since it is just for testing): it won't
// construct the correct result if the input has compound statements.
RewriteRule invertIf() {
  ExprId C;
  StmtId T, E;
  return RewriteRule(ifStmt(hasCondition(C.bind()), hasThen(T.bind()),
                            hasElse(E.bind())))
      .applyAll({TextChange(C).to(Stencil::cat("!(", C, ")")),
                 TextChange(T).to(Stencil::cat(E)),
                 TextChange(E).to(Stencil::cat(T))});
}

TEST_F(TransformerTest, InvertIfMultiChange) {
  std::string Input = R"cc(
    void foo() {
      if (10 > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";
  std::string Expected = R"cc(
    void foo() {
      if (!(10 > 1.0))
        log(0) << "ok";
      else
        log(1) << "oh no!";
    }
  )cc";

  Transformer T(invertIf(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}


// Use the lvalue-ref overloads of the builder methods.
RewriteRule invertIfLvalue() {
  ExprId C;
  StmtId T, E;
  RewriteRule R(
      ifStmt(hasCondition(C.bind()), hasThen(T.bind()), hasElse(E.bind())));
  TextChange Change = changeAll();
  Change.setReplacement(Stencil::cat("if(!(", C, ")) ", E, " else ", T));
  Change.setExplanation("message");
  R.apply(Change);
  return R;
}

TEST_F(TransformerTest, InvertIfLvalue) {
  std::string Input = R"cc(
    void foo() {
      if (10 > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";
  std::string Expected = R"cc(
    void foo() {
      if (!(10 > 1.0))
        log(0) << "ok";
      else
        log(1) << "oh no!";
    }
  )cc";

  Transformer T(invertIfLvalue(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

//
// (ProtoCommandLineFlag f){ $f.foo() } => { $f.GetProto().foo() }
//
RewriteRule ruleFlag() {
  ExprId Flag;
  return RewriteRule(
             cxxMemberCallExpr(
                 on(expr(Flag.bind(), hasType(cxxRecordDecl(hasName(
                                          "proto::ProtoCommandLineFlag"))))),
                 unless(callee(cxxMethodDecl(hasName("GetProto"))))))
      .apply(TextChange(Flag)
                  .to(Stencil::cat(Flag, ".GetProto()"))
                  .because("Use GetProto() to access proto fields."));
}

TEST_F(TransformerTest, Flag) {
  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
  )cc";
  std::string Expected = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.GetProto().foo();
    int y = flag.GetProto().foo();
  )cc";

  Transformer T(ruleFlag(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Convenience definition for readability.
static Stencil goodText() { return Stencil::cat("good"); }

RewriteRule ruleChangeFunctionName() {
  DeclId Fun;
  return RewriteRule(functionDecl(hasName("bad"), Fun.bind()))
      .apply(TextChange(Fun, NodePart::kName).to(goodText()));
}

TEST_F(TransformerTest, NodePartNameNamedDecl) {
  std::string Input = R"cc(
    int bad(int x);
    int bad(int x) { return x * x; }
  )cc";
  std::string Expected = R"cc(
    int good(int x);
    int good(int x) { return x * x; }
  )cc";

  Transformer T(ruleChangeFunctionName(), changeRecorder());
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
      RewriteRule(declRefExpr(to(functionDecl(hasName("bad"))), Ref.bind()))
      .apply(TextChange(Ref, NodePart::kName).to(goodText())),
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
  Transformer T(RewriteRule(declRefExpr(to(functionDecl()), Ref.bind()))
                .apply(TextChange(Ref, NodePart::kName).to(goodText())),
                changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Input, rewrite(Input));
}

RewriteRule ruleChangeFieldName() {
  ExprId E;
  return RewriteRule(memberExpr(member(hasName("bad")), E.bind()))
      .apply(TextChange(E, NodePart::kMember).to(goodText()));
}

TEST_F(TransformerTest, NodePartMember) {
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

  Transformer T(ruleChangeFieldName(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, NodePartExpansion) {
  DeclId Fun;
  auto Rule = RewriteRule(functionDecl(hasName("bad"), Fun.bind()))
                  .apply(TextChange(Fun, NodePart::kExpansion).to(goodText()));

  std::string Input = R"cc(
#define BADDECL(E) int bad(int x) { return E; }
    BADDECL(x * x)
  )cc";
  std::string Expected = R"cc(
#define BADDECL(E) int bad(int x) { return E; }
    good
  )cc";

  Transformer T(Rule, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests the MultiTransformer class and, generally, the combination of multiple
// rules.
TEST_F(TransformerTest, MultiRule) {
  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
    int f(string s) { return strlen(s.c_str()); }
  )cc";
  std::string Expected = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.GetProto().foo();
    int y = flag.GetProto().foo();
    int f(string s) { return s.size(); }
  )cc";

  std::vector<RewriteRule> Rules;
  Rules.emplace_back(ruleStrlenSize());
  Rules.emplace_back(ruleFlag());
  MultiTransformer T(std::move(Rules), changeRecorder(), &MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, RuleSetFirstUnrelated) {
  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
    int f(string s) { return strlen(s.c_str()); }
  )cc";
  std::string Expected = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.GetProto().foo();
    int y = flag.GetProto().foo();
    int f(string s) { return s.size(); }
  )cc";

  auto Rules = RewriteRuleSet::firstOf({ruleStrlenSize(), ruleFlag()});
  ASSERT_TRUE(Rules.hasValue());
  Transformer T(*Rules, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Version of ruleStrlenSizeAny that inserts a method with a different name than
// ruleStrlenSize, so we can tell their effect apart.
RewriteRule ruleStrlenSizeAnyDistinct() {
  ExprId S;
  return RewriteRule(
             callExpr(
                 callee(functionDecl(hasName("strlen"))),
                 hasArgument(0, cxxMemberCallExpr(
                                    on(S.bind()),
                                    callee(cxxMethodDecl(hasName("c_str")))))))
      .apply(
          changeAll()
              .to(Stencil::cat(S, ".supersize()"))
              .because("Call supersize() method directly on object '", S, "'"));
}

TEST_F(TransformerTest, RuleSetFirstRelated) {
  std::string Input = R"cc(
    namespace foo {
    struct mystring {
      char* c_str();
    };
    int f(mystring s) { return strlen(s.c_str()); }
    } // namespace foo
    int g(string s) { return strlen(s.c_str()); }
  )cc";
  std::string Expected = R"cc(
    namespace foo {
    struct mystring {
      char* c_str();
    };
    int f(mystring s) { return s.supersize(); }
    } // namespace foo
    int g(string s) { return s.size(); }
  )cc";

  auto Rules =
      RewriteRuleSet::firstOf({ruleStrlenSize(), ruleStrlenSizeAnyDistinct()});
  ASSERT_TRUE(Rules.hasValue());
  Transformer T(*Rules, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Change the order of the rules to get a different result.
TEST_F(TransformerTest, RuleSetFirstRelatedSwapped) {
  std::string Input = R"cc(
    namespace foo {
    struct mystring {
      char* c_str();
    };
    int f(mystring s) { return strlen(s.c_str()); }
    } // namespace foo
    int g(string s) { return strlen(s.c_str()); }
  )cc";
  std::string Expected = R"cc(
    namespace foo {
    struct mystring {
      char* c_str();
    };
    int f(mystring s) { return s.supersize(); }
    } // namespace foo
    int g(string s) { return s.supersize(); }
  )cc";

  auto Rules =
      RewriteRuleSet::firstOf({ruleStrlenSizeAnyDistinct(), ruleStrlenSize()});
  ASSERT_TRUE(Rules.hasValue());
  Transformer T(*Rules, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

TEST_F(TransformerTest, RuleSetEach) {
  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
    int f(string s) { return strlen(s.c_str()); }
  )cc";
  std::string Expected = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.GetProto().foo();
    int y = flag.GetProto().foo();
    int f(string s) { return s.size(); }
  )cc";

  auto Rules = RewriteRuleSet::eachOf({ruleStrlenSize(), ruleFlag()});
  ASSERT_TRUE(Rules.hasValue());
  Transformer T(*Rules, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// A rule that finds function calls with two arguments where the arguments are
// the same identifier.
RewriteRule ruleDuplicateArgs() {
  ExprId Arg0, Arg1;
  return RewriteRule(callExpr(argumentCountIs(2), hasArgument(0, Arg0.bind()),
                              hasArgument(1, Arg1.bind())))
      .where([Arg0, Arg1](
                 const clang::ast_matchers::MatchFinder::MatchResult &result) {
        auto *Ref0 = Arg0.getNodeAs<clang::DeclRefExpr>(result);
        auto *Ref1 = Arg1.getNodeAs<clang::DeclRefExpr>(result);
        return Ref0 != nullptr && Ref1 != nullptr &&
               Ref0->getDecl() == Ref1->getDecl();
      })
      .apply(changeAll().to(goodText()));
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
    int z = good;
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

// Verifies that no transformation is applied even when matching text is the
// complete expansion.
TEST_F(TransformerTest, NoTransformationInMacroFull) {
  std::string Input = R"cc(
#define MACRO(str) strlen((str).c_str())
    int f(string s) { return MACRO(s); })cc";

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
}

// Verifies that no transformation is applied when matching text is part of the
// expansion.
TEST_F(TransformerTest, NoTransformationInMacroPartial) {
  std::string Input = R"cc(
#define MACRO(str) strlen((str).c_str()) + 3
    int f(string s) { return MACRO(s); })cc";

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
}

// Verifies that a macro is not replaced when it's a part of a match.
TEST_F(TransformerTest, NoTransformationInMacroForPart) {
  std::string Input = R"cc(
#define BADNAME bad
    int BADNAME(float* x);
  )cc";

  Transformer T(ruleChangeFunctionName(), changeRecorder());
  T.registerMatchers(&MatchFinder);
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

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
}

//
// Complex tests which are more examples than actual unit tests.
//

static TextChange insertAfter(const NodeId& Node, Stencil S) {
  return TextChange(Node, NodePart::kAfter).to(std::move(S));
}

// Split the one rule into two, to handle the iteration over all constructors
// separately from the singleton edits.
TEST_F(TransformerTest, ComplexMultichangeEditAndInsertion) {
  using namespace ::clang::ast_matchers;

  std::string Input = R"cc(
    class Derived : public Base {
    public:
      Derived(int x) {}
      Derived(int x, int y) {}
      ~Derived() {}

      int Foo() override { return 4; }
      int Bar(int x) override { return x; }
    };
  )cc";

  std::string Expected = R"cc(
    class DerivedFoo : public Base {
    public:
      DerivedFoo(int x) {}
      DerivedFoo(int x, int y) {}
      ~DerivedFoo() {}

      int Foo() override { return 4; }
    };
    class DerivedBar : public BarBase {
    public:
      DerivedBar() {}
      ~DerivedBar() override {}
      int Bar(int x) override { return x; }
    };
  )cc";

  std::vector<RewriteRule> Rules;
  DeclId DerivedClass, Constructor, Destructor, BarMethod;
  auto ClassMatcher = cxxRecordDecl(
      isDerivedFrom("Base"),
      DerivedClass.bind(),
      hasDescendant(cxxDestructorDecl(Destructor.bind())),
      hasDescendant(cxxMethodDecl(hasName("Bar"), BarMethod.bind())));
  Rules.push_back(
      RewriteRule(ClassMatcher)
          .applyAll({TextChange(DerivedClass, NodePart::kName)
                         .to(Stencil::cat(name(DerivedClass), "Foo")),
                     TextChange(Destructor, NodePart::kName)
                     .to(Stencil::cat("~", name(DerivedClass), "Foo")),
                     // Deletion:
                     TextChange(BarMethod).to(Stencil())}));

  Rules.push_back(
      RewriteRule(cxxRecordDecl(isDerivedFrom("Base"), DerivedClass.bind(),
                                forEachDescendant(
                                    cxxConstructorDecl(Constructor.bind()))))
          .apply(TextChange(Constructor, NodePart::kName)
                     .to(Stencil::cat(name(DerivedClass), "Foo"))));

  Rules.push_back(
      RewriteRule(ClassMatcher)
          .apply(insertAfter(DerivedClass, Stencil::cat(";")))
          .apply(insertAfter(DerivedClass,
                             Stencil::cat("class ", name(DerivedClass),
                                          "Bar : public BarBase { ",
                                          "public: ",                      //
                                          name(DerivedClass), "Bar() {} ", //
                                          "~", name(DerivedClass), "Bar()",
                                          " override {}", //
                                          BarMethod, "}"))));

  auto RuleSet = RewriteRuleSet::eachOf(std::move(Rules));
  assert(RuleSet &&
         "All rules in Rules should be constructed to have the same kind.");
  Transformer T(*RuleSet, changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

RewriteRule editRuleWithCopy() {
  using namespace ::clang::ast_matchers;

  DeclId DerivedClass, Constructor, Destructor, BarMethod;
  auto ClassMatcher = cxxRecordDecl(
      isDerivedFrom("Base"), DerivedClass.bind(),
      forEachDescendant(
          cxxConstructorDecl(unless(isImplicit()), Constructor.bind())),
      hasDescendant(cxxDestructorDecl(Destructor.bind())),
      hasDescendant(cxxMethodDecl(hasName("Bar"), BarMethod.bind())));

  // TODO: change derivation to public FooBase. Need selectors for that. Or, a
  // generator that grabs all the decls in the body of the class (just like
  // args, statements).
  return RewriteRule(ClassMatcher)
      .apply(TextChange(DerivedClass, NodePart::kAfter).to(Stencil::cat(";")))
      .apply(TextChange(DerivedClass, NodePart::kAfter)
                 .to(rewriteNode(
                     DerivedClass.id(),
                     {TextChange(DerivedClass, NodePart::kName)
                          .to(Stencil::cat(name(DerivedClass), "Foo")),
                      TextChange(Constructor, NodePart::kName)
                          .to(Stencil::cat(name(DerivedClass), "Foo")),
                      TextChange(Destructor, NodePart::kName)
                          .to(Stencil::cat("~", name(DerivedClass), "Foo")),
                      // Deletion:
                      TextChange(BarMethod).to(Stencil())})));
}

TEST_F(TransformerTest, ComplexMultichangeEditCopy) {
  std::string Input = R"cc(
    class Derived : public Base {
    public:
      Derived(int x) {}
      ~Derived() {}

      int Foo() override { return 4; }
      int Bar(int x) override { return x; }
    };
  )cc";

  std::string Expected = R"cc(
    class Derived : public Base {
    public:
      Derived(int x) {}
      ~Derived() {}

      int Foo() override { return 4; }
      int Bar(int x) override { return x; }
    };
    class DerivedFoo : public Base {
    public:
      DerivedFoo(int x) {}
      ~DerivedFoo() {}

      int Foo() override { return 4; }
    };
  )cc";

  Transformer T(editRuleWithCopy(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

//
// maybeTransform tests
//

// Formats an Optional<string> for error messages.
std::string errString(const llvm::Optional<std::string> &O) {
  return O ? "Some " + *O : "None";
}

class MaybeTransformTest : public ::testing::Test {
protected:
  // We need to initialize nodes_ here because Node has no default constructor.
  MaybeTransformTest() : Node(init()) {}

  // Also initializes AstUnit.
  clang::ast_type_traits::DynTypedNode init() {
    std::string Code = R"cc(
      int strlen(char*);
      namespace foo {
      struct mystring {
        char* c_str();
      };
      int f(mystring s) { return strlen(s.c_str()); }
      }  // namespace foo)cc";
    AstUnit = buildASTFromCode(Code);
    assert(AstUnit != nullptr && "AST not constructed");

    auto Matches = clang::ast_matchers::match(
        returnStmt(hasReturnValue(callExpr().bind("expr"))), *context());
    assert(Matches.size() == 1);
    auto It = Matches[0].getMap().find("expr");
    assert(It != Matches[0].getMap().end() && "Match failure");
    return It->second;
  }

  // Convenience method.
  clang::ASTContext *context() { return &AstUnit->getASTContext(); }

  std::unique_ptr<clang::ASTUnit> AstUnit;
  clang::ast_type_traits::DynTypedNode Node;
};

// Tests case where rewriting succeeds and the rule is applied.
TEST_F(MaybeTransformTest, SuccessRuleApplies) {
  auto ResultOrErr = maybeTransform(ruleStrlenSizeAny(), Node, context());
  if (auto Err = ResultOrErr.takeError()) {
    GTEST_FAIL() << "Rewrite failed: " << llvm::toString(std::move(Err));
  }
  auto &Result = *ResultOrErr;
  EXPECT_THAT(Result, ElementsAre(testing::Eq("s.size()")));
}

TEST_F(MaybeTransformTest, SuccessRuleAppliesEdit) {
  using namespace ::clang::ast_matchers;

  StmtId Callee("callee");
  ExprId S("string");
  auto EditRule =
      RewriteRule(
          callExpr(
              callee(functionDecl(hasName("strlen"))), callee(Callee.bind()),
              hasArgument(0, cxxMemberCallExpr(
                                 on(S.bind()),
                                 callee(cxxMethodDecl(hasName("c_str")))))))
          .applyAll({TextChange(Callee).to(Stencil::cat("StringLength")),
                     TextChange(S).to(Stencil::cat("FooString"))});

  auto ResultOrErr = maybeTransform(EditRule, Node, context());
  if (auto Err = ResultOrErr.takeError()) {
    GTEST_FAIL() << "Rewrite failed: " << llvm::toString(std::move(Err));
  }
  auto &Result = *ResultOrErr;
  EXPECT_THAT(Result,
              ElementsAre(testing::Eq("StringLength(FooString.c_str())")));
}

#if 0
TEST_F(MaybeTransformTest, SuccessRuleDoesNotApply) {
  auto Rule = RewriteRule(callExpr(callee(functionDecl(hasName("foo")))))
                  .replaceWith("bar()");
  auto ResultOrErr = maybeTransform(Rule, Node, context());
  if (auto Err = ResultOrErr.takeError()) {
    GTEST_FAIL() << "Rewrite failed: " << llvm::toString(std::move(Err));
  }
  auto &Result = *ResultOrErr;
  EXPECT_EQ(Result, llvm::None) << "Actual result is: " << errString(Result);
}

TEST_F(MaybeTransformTest, FailureUnbound) {
  using stencil_generators::id;
  // Note: pattern needs to bind at least on id or the match will return no
  // results.
  auto Rule = RewriteRule()
                  .matching(expr().bind("e"))
                  .replaceWith(id("unbound"), ".size()");
  auto ResultOrErr = maybeTransform(Rule, Node, context());
  EXPECT_TRUE(llvm::errorToBool(ResultOrErr.takeError()))
      << "Expected rewrite to fail on unbound node: "
      << errString(*ResultOrErr);
}

TEST_F(MaybeTransformTest, FailureMultiMatch) {
  auto Rule = RewriteRule()
                  .matching(stmt(eachOf(callExpr().bind("expr"),
                                        has(callExpr().bind("expr")))))
                  .replaceWith(stencil_generators::id("expr"), ".size()");
  auto ResultOrErr = maybeTransform(Rule, Node, context());
  EXPECT_TRUE(llvm::errorToBool(ResultOrErr.takeError()))
      << "Expected rewrite to fail on too many matches: "
      << errString(*ResultOrErr);
}
#endif
} // namespace tooling
} // namespace clang
