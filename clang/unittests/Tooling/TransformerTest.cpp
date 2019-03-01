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

static TextChange changeAll() { return TextChange(RewriteRule::rootId()); }

// Change strlen($s.c_str()) to $s.size().
RewriteRule ruleStrlenSizeAny() {
  ExprId S;
  return RewriteRule()
      .matching(callExpr(
          callee(functionDecl(hasName("strlen"))),
          hasArgument(
              0, cxxMemberCallExpr(on(S.bind()),
                                   callee(cxxMethodDecl(hasName("c_str")))))))
      .change(changeAll()
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

TEST_F(TransformerTest, StrlenSizePointer) {
  std::string Input = "int f(string* s) { return strlen(s->c_str()); }";
  std::string Expected = "int f(string* s) { return s->size(); }";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}
#if 0
// Variant of StrlenSizePointer where the source is more verbose. We check for
// the same result.
TEST_F(TransformerTest, StrlenSizePointerExplicit) {
  std::string Input = "int f(string* s) { return strlen((*s).c_str()); }";
  std::string Expected = "int f(string* s) { return s->size(); }";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests that code that looks the same but involves another type, even with the
// (unqualified) name "string", does not match.
TEST_F(TransformerTest, OtherStringType) {
  std::string Input =
      R"cc(namespace foo {
           struct string {
             char* c_str();
           };
           int f(string s) { return strlen(s.c_str()); }
           }  // namespace foo)cc";

  Transformer T(ruleStrlenSize(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // Input should not be changed.
  compareSnippets(Input, rewrite(Input));
}
#endif

// Tests that expressions in macro arguments are rewritten (when applicable).
TEST_F(TransformerTest, StrlenSizeMacro) {
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

#if 0
// RuleStrlenSize, but where the user manually manages the AST node ids.
RewriteRule ruleStrlenSizeManual() {
  auto StringType = namedDecl(hasAnyName("::basic_string", "::string"));
  return makeRule(
      callExpr(callee(functionDecl(hasName("strlen"))),
               hasArgument(
                   0, cxxMemberCallExpr(
                          on(id("s", expr(hasType(isOrPointsTo(StringType))))),
                          callee(cxxMethodDecl(hasName("c_str")))))),
      Stencil::cat(member("s", "size()")),
      "Use size() method directly on string.");
}

TEST_F(TransformerTest, StrlenSizeManual) {
  std::string Input = "int f(string s) { return strlen(s.c_str()); }";
  std::string Expected = "int f(string s) { return s.size(); }";

  Transformer T(ruleStrlenSizeManual(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}
#endif

RewriteRule ruleRenameFunctionAddHeader() {
  ExprId Arg;
  return RewriteRule()
      .matching(callExpr(callee(functionDecl(hasName("update"))),
                         hasArgument(0, Arg.bind())))
      .addHeader("foo/updater.h")
      .change(changeAll().to(Stencil::cat("updateAddress(", Arg, ")")));
}

RewriteRule ruleRenameFunctionRemoveHeader() {
  ExprId Arg;
  return RewriteRule()
      .matching(callExpr(callee(functionDecl(hasName("updateAddress"))),
                         hasArgument(0, Arg.bind())))
      .removeHeader("foo/updater.h")
      .change(changeAll().to(Stencil::cat("update(", Arg, ")")));
}

RewriteRule ruleRenameFunctionChangeHeader() {
  ExprId Arg;
  return RewriteRule()
      .matching(callExpr(callee(functionDecl(hasName("update"))),
                         hasArgument(0, Arg.bind())))
      .removeHeader("bar/updater.h")
      .addHeader("foo/updater.h")
      .change(changeAll().to(Stencil::cat("updateAddress(", Arg, ")")));
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

#if 0
//
// Inspired by a clang-tidy request:
//
// Change if ($e) {log($level) << $msg;} to
//    LOG_IF($level, $e) << $msg;
//
// We use a function, log(), rather than a macro, LOG(), to simplify the matcher
// needed.
RewriteRule ruleLogIf() {
  ExprId Condition;
  ExprId Level;
  ExprId Msg;
  auto LogCall = callExpr(callee(functionDecl(hasName("log"))),
                          hasArgument(0, Level.bind()));
  return makeRule(
      ifStmt(hasCondition(Condition.bind()),
             hasThen(expr(ignoringImplicit(cxxOperatorCallExpr(
                 hasOverloadedOperatorName("<<"), hasArgument(0, LogCall),
                 hasArgument(1, Msg.bind()))))),
             unless(hasElse(expr()))),
      Stencil::cat("LOG_IF(", Level, ", ", parens(Condition), ") << ", Msg, ";"),
      "Use LOG_IF() when LOG() is only member of if statement.");
}

TEST_F(TransformerTest, LogIf) {
  std::string Input = R"cc(
    double x = 3.0;
    void foo() {
      if (x > 1.0) log(1) << "oh no!";
    }
    void bar() {
      if (x > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";
  std::string Expected = R"cc(
    double x = 3.0;
    void foo() { LOG_IF(1, (x > 1.0)) << "oh no!"; }
    void bar() {
      if (x > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";

  Transformer T(ruleLogIf(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

// Tests RuleLogIf when we expect the output condition not to be wrapped in
// parens.
TEST_F(TransformerTest, LogIfNoParens) {
  std::string Input = R"cc(
    double x = 3.0;
    void foo() {
      bool condition = x > 1.0;
      if (condition) log(1) << "oh no!";
    }
    void bar() {
      if (x > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";
  std::string Expected = R"cc(
    double x = 3.0;
    void foo() {
      bool condition = x > 1.0;
      LOG_IF(1, condition) << "oh no!";
    }
    void bar() {
      if (x > 1.0)
        log(1) << "oh no!";
      else
        log(0) << "ok";
    }
  )cc";

  Transformer T(ruleLogIf(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}
#endif

// Change `if ($c) $t $e` to `if (!$c) $e $t`.
//
// N.B. This rule is oversimplified (since it is just for testing): it won't
// construct the correct result if the input has compound statements.
RewriteRule invertIf() {
  ExprId C;
  StmtId T, E;
  return RewriteRule()
      .matching(
          ifStmt(hasCondition(C.bind()), hasThen(T.bind()), hasElse(E.bind())))
      .change(TextChange(C).to(Stencil::cat("!(", C, ")")))
      .change(TextChange(T).to(Stencil::cat(E)))
      .change(TextChange(E).to(Stencil::cat(T)));
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

#if 0
// Use the lvalue-ref overloads of the RewriteRule builder methods.
RewriteRule invertIfLvalue() {
  ExprId C;
  StmtId T, E;
  RewriteRule Rule;
  Rule.matching(
          ifStmt(hasCondition(C.bind()), hasThen(T.bind()), hasElse(E.bind())))
      .replaceWith("if(!(", C, ")) ", E, " else ", T);
  return Rule;
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
  return RewriteRule()
      .matching(cxxMemberCallExpr(
          on(expr(Flag.bind(), hasType(cxxRecordDecl(
                                   hasName("proto::ProtoCommandLineFlag"))))),
          unless(callee(cxxMethodDecl(hasName("GetProto"))))))
      .change(Flag)
      .replaceWith(Flag, ".GetProto()")
      .explain("Use GetProto() to access proto fields.");
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

// Variant of RuleFlag that doesn't rely on specifying a particular
// target. Instead, we explicitly bind the decl of the invoked method and refer
// to it in the code using the Name() operator.
RewriteRule ruleFlagNoTarget() {
  ExprId Flag;
  DeclId Method;
  return makeRule(
      cxxMemberCallExpr(
          on(bind(Flag, expr(hasType(cxxRecordDecl(
                            hasName("proto::ProtoCommandLineFlag")))))),
          callee(bind(Method, cxxMethodDecl(unless(hasName("GetProto"))))),
          argumentCountIs(0)),
      Stencil::cat(addInclude("fake/for/test.h"), member(Flag, "GetProto()"),
                   ".", name(Method), "()"),
      "Use GetProto() to access proto fields.");
}

// Tests use of Name() operator.
TEST_F(TransformerTest, FlagWithName) {
  std::string Input = R"cc(
    proto::ProtoCommandLineFlag flag;
    int x = flag.foo();
    int y = flag.GetProto().foo();
  )cc";
  std::string Expected =
      R"cc(#include "fake/for/test.h"

           proto::ProtoCommandLineFlag flag;
           int x = flag.GetProto().foo();
           int y = flag.GetProto().foo();
      )cc";

  Transformer T(ruleFlagNoTarget(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Expected, rewrite(Input));
}

RewriteRule ruleChangeFunctionName() {
  DeclId Fun;
  return RewriteRule()
      .matching(functionDecl(hasName("bad"), Fun.bind()))
      .change(Fun, NodePart::kName)
      .replaceWith("good");
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
      RewriteRule()
          .matching(declRefExpr(to(functionDecl(hasName("bad"))), Ref.bind()))
          .change(Ref, NodePart::kName)
          .replaceWith("good"),
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
                    .replaceWith("good"),
                changeRecorder());
  T.registerMatchers(&MatchFinder);
  compareSnippets(Input, rewrite(Input));
}

RewriteRule ruleChangeFieldName() {
  ExprId E;
  return RewriteRule()
      .matching(memberExpr(member(hasName("bad")), E.bind()))
      .change(E, NodePart::kMember)
      .replaceWith("good");
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
      .replaceWith("42");
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

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
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

  Transformer T(ruleStrlenSizeAny(), changeRecorder());
  T.registerMatchers(&MatchFinder);
  // The macro should be ignored.
  compareSnippets(Input, rewrite(Input));
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

// A very simple matcher for llvm::Optional values.
MATCHER_P(IsSomething, ValueMatcher, "") {
  if (!arg)
    return false;
  return ::testing::ExplainMatchResult(ValueMatcher, *arg, result_listener);
}

// Tests case where rewriting succeeds and the rule is applied.
TEST_F(MaybeTransformTest, SuccessRuleApplies) {
  auto ResultOrErr = maybeTransform(ruleStrlenSizeAny(), Node, context());
  if (auto Err = ResultOrErr.takeError()) {
    GTEST_FAIL() << "Rewrite failed: " << llvm::toString(std::move(Err));
  }
  auto &Result = *ResultOrErr;
  EXPECT_THAT(Result, IsSomething(testing::Eq("s.size()")));
}

TEST_F(MaybeTransformTest, SuccessRuleDoesNotApply) {
  auto Rule = RewriteRule()
                  .matching(callExpr(callee(functionDecl(hasName("foo")))))
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
