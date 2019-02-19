//===- unittest/Tooling/StencilTest.cpp -----------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "clang/Tooling/Refactoring/Stencil.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Tooling/FixIt.h"
#include "clang/Tooling/Tooling.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"

namespace clang {
namespace tooling {
namespace {

using ::clang::ast_matchers::compoundStmt;
using ::clang::ast_matchers::decl;
using ::clang::ast_matchers::declStmt;
using ::clang::ast_matchers::expr;
using ::clang::ast_matchers::hasAnySubstatement;
using ::clang::ast_matchers::hasCondition;
using ::clang::ast_matchers::hasDescendant;
using ::clang::ast_matchers::hasElse;
using ::clang::ast_matchers::hasInitializer;
using ::clang::ast_matchers::hasName;
using ::clang::ast_matchers::hasReturnValue;
using ::clang::ast_matchers::hasSingleDecl;
using ::clang::ast_matchers::hasThen;
using ::clang::ast_matchers::ifStmt;
using ::clang::ast_matchers::ignoringImplicit;
using ::clang::ast_matchers::returnStmt;
using ::clang::ast_matchers::stmt;
using ::clang::ast_matchers::varDecl;

using MatchResult = ::clang::ast_matchers::MatchFinder::MatchResult;

using ::clang::tooling::stencil_generators::addInclude;
using ::clang::tooling::stencil_generators::apply;
using ::clang::tooling::stencil_generators::args;
using ::clang::tooling::stencil_generators::asAddress;
using ::clang::tooling::stencil_generators::asValue;
using ::clang::tooling::stencil_generators::member;
using ::clang::tooling::stencil_generators::name;
using ::clang::tooling::stencil_generators::node;
using ::clang::tooling::stencil_generators::parens;
using ::clang::tooling::stencil_generators::removeInclude;
using ::clang::tooling::stencil_generators::text;

using ::testing::Eq;
using ::testing::Ne;

// We can't directly match on llvm::Expected since its accessors mutate the
// object. So, we collapse it to an Optional.
llvm::Optional<std::string> toOptional(llvm::Expected<std::string> V) {
  if (V)
    return *V;
  ADD_FAILURE() << "Losing error in conversion to IsSomething: "
                << llvm::toString(V.takeError());
  return llvm::None;
}

// A very simple matcher for llvm::Optional values.
MATCHER_P(IsSomething, ValueMatcher, "") {
  if (!arg)
    return false;
  return ::testing::ExplainMatchResult(ValueMatcher, *arg, result_listener);
}

// Create a valid translation-unit from a statement.
std::string wrapSnippet(llvm::StringRef StatementCode) {
  return ("auto stencil_test_snippet = []{" + StatementCode + "};").str();
}

clang::ast_matchers::DeclarationMatcher
wrapMatcher(const clang::ast_matchers::StatementMatcher &Matcher) {
  return varDecl(hasName("stencil_test_snippet"),
                 hasDescendant(compoundStmt(hasAnySubstatement(Matcher))));
}

struct TestMatch {
  // The AST unit from which `result` is built. We bundle it because it backs
  // the result. Users are not expected to access it.
  std::unique_ptr<clang::ASTUnit> AstUnit;
  // The result to use in the test. References `ast_unit`.
  MatchResult Result;
};

// Matches `matcher` against the statement `statement_code` and returns the
// result. Handles putting the statement inside a function and modifying the
// matcher correspondingly. `matcher` should match `statement_code` exactly --
// that is, produce exactly one match.
llvm::Optional<TestMatch>
matchStmt(llvm::StringRef StatementCode,
          clang::ast_matchers::StatementMatcher Matcher) {
  auto AstUnit = buildASTFromCode(wrapSnippet(StatementCode));
  if (AstUnit == nullptr) {
    ADD_FAILURE() << "AST construction failed";
    return llvm::None;
  }
  clang::ASTContext &Context = AstUnit->getASTContext();
  auto Matches = clang::ast_matchers::match(wrapMatcher(Matcher), Context);
  // We expect a single, exact match for the statement.
  if (Matches.size() != 1) {
    ADD_FAILURE() << "Wrong number of matches: " << Matches.size();
    return llvm::None;
  }
  return TestMatch{std::move(AstUnit), MatchResult(Matches[0], &Context)};
}

class StencilTest : public ::testing::Test {
public:
  StencilTest() : Id0("id0"), Id1("id1") {}

protected:
  // Verifies that filling a single-parameter stencil from `context` will result
  // in `expected`, assuming that the code in `context` contains a statement
  // `return e` and "id0" is bound to `e`.
  void testSingle(llvm::StringRef Snippet, const Stencil &Stencil,
                  llvm::StringRef Expected) {
    auto StmtMatch = matchStmt(
        Snippet,
        returnStmt(hasReturnValue(ignoringImplicit(expr().bind(Id0.id())))));
    ASSERT_TRUE(StmtMatch);
    EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
                IsSomething(Expected));
    EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
    EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
  }

  // Verifies that the given stencil fails when evaluated on a valid match
  // result. Binds a statement to "stmt", a (non-member) ctor-initializer to
  // "init", an expression to "expr" and a (nameless) declaration to "decl".
  void testError(const Stencil &Stencil,
                 testing::Matcher<std::string> Matcher) {
    using ::clang::ast_matchers::cxxConstructExpr;
    using ::clang::ast_matchers::cxxCtorInitializer;
    using ::clang::ast_matchers::hasDeclaration;
    using ::clang::ast_matchers::isBaseInitializer;

    const std::string Snippet = R"cc(
      struct A {};
      class F : public A {
       public:
        F(int) {}
      };
      F(1);
    )cc";
    auto StmtMatch = matchStmt(
        Snippet,
        stmt(hasDescendant(
                 cxxConstructExpr(
                     hasDeclaration(decl(hasDescendant(cxxCtorInitializer(
                                                           isBaseInitializer())
                                                           .bind("init")))
                                        .bind("decl")))
                     .bind("expr")))
            .bind("stmt"));
    ASSERT_TRUE(StmtMatch);
    if (auto ResultOrErr = Stencil.eval(StmtMatch->Result)) {
      ADD_FAILURE() << "Expected failure but succeeded: " << *ResultOrErr;
    } else {
      auto Err = llvm::handleErrors(ResultOrErr.takeError(),
                                    [&Matcher](const llvm::StringError &Err) {
                                      EXPECT_THAT(Err.getMessage(), Matcher);
                                    });
      if (Err) {
        ADD_FAILURE() << "Unhandled error: " << llvm::toString(std::move(Err));
      }
    }
  }

  // Tests failures caused by references to unbound nodes. `unbound_id` is the
  // id that will cause the failure.
  void testUnboundNodeError(const Stencil &Stencil, llvm::StringRef UnboundId) {
    testError(Stencil, testing::AllOf(testing::HasSubstr(UnboundId),
                                      testing::HasSubstr("not bound")));
  }

  NodeId Id0;
  NodeId Id1;
};

TEST_F(StencilTest, SingleStatement) {
  using stencil_generators::id;

  const std::string Snippet = R"cc(
    if (true)
      return 1;
    else
      return 0;
  )cc";
  auto StmtMatch = matchStmt(Snippet, ifStmt(hasCondition(stmt().bind("a1")),
                                             hasThen(stmt().bind("a2")),
                                             hasElse(stmt().bind("a3"))));
  ASSERT_TRUE(StmtMatch);
  auto Stencil =
      Stencil::cat("if(!", id("a1"), ") ", id("a3"), "; else ", id("a2"));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("if(!true) return 0; else return 1")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, UnboundNode) {
  using stencil_generators::id;

  const std::string Snippet = R"cc(
    if (true)
      return 1;
    else
      return 0;
  )cc";
  auto StmtMatch = matchStmt(Snippet, ifStmt(hasCondition(stmt().bind("a1")),
                                             hasThen(stmt().bind("a2"))));
  ASSERT_TRUE(StmtMatch);
  auto Stencil = Stencil::cat("if(!", id("a1"), ") ", id("UNBOUND"), ";");
  auto ResultOrErr = Stencil.eval(StmtMatch->Result);
  EXPECT_TRUE(llvm::errorToBool(ResultOrErr.takeError()))
      << "Expected unbound node, got " << *ResultOrErr;
}

TEST_F(StencilTest, NodeOp) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(node(Id0)), "x");
  testSingle(Snippet, Stencil::cat(node("id0")), "x");
}

TEST_F(StencilTest, MemberOpValue) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(member(Id0, "field")), "x.field");
}

TEST_F(StencilTest, MemberOpValueExplicitText) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(member(Id0, text("field"))), "x.field");
}

TEST_F(StencilTest, MemberOpValueAddress) {
  const std::string Snippet = R"cc(
    int x;
    return &x;
  )cc";
  testSingle(Snippet, Stencil::cat(member(Id0, "field")), "x.field");
}

TEST_F(StencilTest, MemberOpPointer) {
  const std::string Snippet = R"cc(
    int *x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(member(Id0, "field")), "x->field");
}

TEST_F(StencilTest, MemberOpPointerDereference) {
  const std::string Snippet = R"cc(
    int *x;
    return *x;
  )cc";
  testSingle(Snippet, Stencil::cat(member(Id0, "field")), "x->field");
}

TEST_F(StencilTest, MemberOpThis) {
  using clang::ast_matchers::hasObjectExpression;
  using clang::ast_matchers::memberExpr;

  const std::string Snippet = R"cc(
    class C {
     public:
      int x;
      int foo() { return x; }
    };
  )cc";
  auto StmtMatch = matchStmt(
      Snippet, returnStmt(hasReturnValue(ignoringImplicit(
                   memberExpr(hasObjectExpression(expr().bind("obj")))))));
  ASSERT_TRUE(StmtMatch);
  const Stencil Stencil = Stencil::cat(member("obj", "field"));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("field")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, MemberOpUnboundNode) {
  // Mistyped.
  testUnboundNodeError(Stencil::cat(member("decl", "field")), "decl");
  testUnboundNodeError(Stencil::cat(member("unbound", "field")), "unbound");
}

TEST_F(StencilTest, ValueOpValue) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(asValue(Id0)), "x");
}

TEST_F(StencilTest, ValueOpPointer) {
  const std::string Snippet = R"cc(
    int *x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(asValue(Id0)), "*x");
}

TEST_F(StencilTest, ValueOpUnboundNode) {
  // Mistyped.
  testUnboundNodeError(Stencil::cat(asValue("decl")), "decl");
  testUnboundNodeError(Stencil::cat(asValue("unbound")), "unbound");
}

TEST_F(StencilTest, AddressOpValue) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(asAddress(Id0)), "&x");
}

TEST_F(StencilTest, AddressOpPointer) {
  const std::string Snippet = R"cc(
    int *x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(asAddress(Id0)), "x");
}

TEST_F(StencilTest, AddressOpUnboundNode) {
  // Mistyped.
  testUnboundNodeError(Stencil::cat(asAddress("decl")), "decl");
  testUnboundNodeError(Stencil::cat(asAddress("unbound")), "unbound");
}

TEST_F(StencilTest, ParensOpVar) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "x");
}

TEST_F(StencilTest, ParensOpMinus) {
  const std::string Snippet = R"cc(
    int x;
    return -x;
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "(-x)");
}

TEST_F(StencilTest, ParensOpDeref) {
  const std::string Snippet = R"cc(
    int *x;
    return *x;
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "(*x)");
}

TEST_F(StencilTest, ParensOpExpr) {
  const std::string Snippet = R"cc(
    int x;
    int y;
    return x + y;
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "(x + y)");
}

// Tests that parens are not added when the expression already has them.
TEST_F(StencilTest, ParensOpParens) {
  const std::string Snippet = R"cc(
    int x;
    int y;
    return (x + y);
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "(x + y)");
}

TEST_F(StencilTest, ParensOpFun) {
  const std::string Snippet = R"cc(
    int bar(int);
    int x;
    int y;
    return bar(x);
  )cc";
  testSingle(Snippet, Stencil::cat(parens(Id0)), "bar(x)");
}

TEST_F(StencilTest, ParensOpUnboundNode) {
  // Mistyped.
  testUnboundNodeError(Stencil::cat(parens("decl")), "decl");
  testUnboundNodeError(Stencil::cat(parens("unbound")), "unbound");
}

TEST_F(StencilTest, NameOp) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  auto StmtMatch =
      matchStmt(Snippet, declStmt(hasSingleDecl(decl().bind("d"))));
  ASSERT_TRUE(StmtMatch);
  const Stencil Stencil = Stencil::cat(name("d"));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("x")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, NameOpCtorInitializer) {
  using clang::ast_matchers::cxxCtorInitializer;

  const std::string Snippet = R"cc(
    class C {
     public:
      C() : field(3) {}
      int field;
      int foo() { return field; }
    };
  )cc";
  auto StmtMatch = matchStmt(
      Snippet, stmt(hasDescendant(cxxCtorInitializer().bind("init"))));
  ASSERT_TRUE(StmtMatch);
  const Stencil Stencil = Stencil::cat(name("init"));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("field")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, NameOpUnboundNode) {
  // Decl has no name.
  testError(Stencil::cat(name("decl")), testing::HasSubstr("not identifier"));
  // Non-member (hence, no name) initializer.
  testError(Stencil::cat(name("init")),
            testing::HasSubstr("non-member initializer"));
  // Mistyped.
  testUnboundNodeError(Stencil::cat(name("expr")), "expr");
  testUnboundNodeError(Stencil::cat(name("unbound")), "unbound");
}

TEST_F(StencilTest, ArgsOp) {
  const std::string Snippet = R"cc(
    struct C {
      int bar(int, int);
    };
    C x;
    return x.bar(3, 4);
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "3, 4");
}

TEST_F(StencilTest, ArgsOpNoArgs) {
  const std::string Snippet = R"cc(
    struct C {
      int bar();
    };
    C x;
    return x.bar();
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "");
}

TEST_F(StencilTest, ArgsOpNoArgsWithComments) {
  const std::string Snippet = R"cc(
    struct C {
      int bar();
    };
    C x;
    return x.bar(/*empty*/);
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "/*empty*/");
}

// Tests that arguments are extracted correctly when a temporary (with parens)
// is used.
TEST_F(StencilTest, ArgsOpWithParens) {
  const std::string Snippet = R"cc(
    struct C {
      int bar(int, int) { return 3; }
    };
    C x;
    return C().bar(3, 4);
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "3, 4");
}

TEST_F(StencilTest, ArgsOpLeadingComments) {
  const std::string Snippet = R"cc(
    struct C {
      int bar(int, int) { return 3; }
    };
    C x;
    return C().bar(/*leading*/ 3, 4);
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "/*leading*/ 3, 4");
}

TEST_F(StencilTest, ArgsOpTrailingComments) {
  const std::string Snippet = R"cc(
    struct C {
      int bar(int, int) { return 3; }
    };
    C x;
    return C().bar(3 /*trailing*/, 4);
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), "3 /*trailing*/, 4");
}

TEST_F(StencilTest, ArgsOpEolComments) {
  const std::string Snippet = R"cc(
    struct C {
      int bar(int, int) { return 3; }
    };
    C x;
    return C().bar(  // Header
        1,           // foo
        2            // bar
    );
  )cc";
  testSingle(Snippet, Stencil::cat(args(Id0)), R"(  // Header
        1,           // foo
        2            // bar
    )");
}

TEST_F(StencilTest, ArgsOpUnboundNode) {
  // Mistyped.
  testUnboundNodeError(Stencil::cat(args("stmt")), "stmt");
  testUnboundNodeError(Stencil::cat(args("unbound")), "unbound");
}

TEST_F(StencilTest, MemberOpWithNameOp) {
  const std::string Snippet = R"cc(
    int object;
    int* method = &object;
    (void)method;
    return object;
  )cc";
  auto StmtMatch = matchStmt(
      Snippet, declStmt(hasSingleDecl(
                   varDecl(hasInitializer(expr().bind("e"))).bind("d"))));
  ASSERT_TRUE(StmtMatch);
  const Stencil Stencil = Stencil::cat(member("e", name("d")));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("object.method")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, NodeFunctionOp) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  auto SimpleFn = [](const ast_type_traits::DynTypedNode &Node,
                     const ASTContext &Context) {
    return fixit::getText(Node, Context).str();
  };
  testSingle(Snippet, Stencil::cat(apply(SimpleFn, Id0)), "x");
  testSingle(Snippet, Stencil::cat(apply(SimpleFn, "id0")), "x");
}

TEST_F(StencilTest, StringFunctionOp) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  auto SimpleFn = [](llvm::StringRef S) { return (S + " - 3").str(); };
  testSingle(Snippet, Stencil::cat(apply(SimpleFn, Id0)), "x - 3");
  testSingle(Snippet, Stencil::cat(apply(SimpleFn, "id0")), "x - 3");
}

TEST_F(StencilTest, StringFunctionOpNameOp) {
  const std::string Snippet = R"cc(
    int x;
    return x;
  )cc";
  auto SimpleFn = [](llvm::StringRef S) { return (S + " - 3").str(); };
  auto StmtMatch =
      matchStmt(Snippet, declStmt(hasSingleDecl(decl().bind("d"))));
  ASSERT_TRUE(StmtMatch);
  const Stencil Stencil = Stencil::cat(apply(SimpleFn, name("d")));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("x - 3")));
}

TEST_F(StencilTest, AddIncludeOp) {
  const std::string Snippet = R"cc(
    int x;
    return -x;
  )cc";
  auto StmtMatch = matchStmt(Snippet, stmt());
  ASSERT_TRUE(StmtMatch);
  auto Stencil = Stencil::cat(addInclude("include/me.h"), "foo",
                              addInclude("include/metoo.h"));
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("foo")));
  EXPECT_THAT(Stencil.addedIncludes(),
              testing::UnorderedElementsAre("include/me.h", "include/metoo.h"));
  EXPECT_THAT(Stencil.removedIncludes(), testing::IsEmpty());
}

TEST_F(StencilTest, RemoveIncludeOp) {
  const std::string Snippet = R"cc(
    int x;
    return -x;
  )cc";
  auto StmtMatch = matchStmt(Snippet, stmt());
  ASSERT_TRUE(StmtMatch);
  auto Stencil = Stencil::cat(removeInclude("include/me.h"), "foo");
  EXPECT_THAT(toOptional(Stencil.eval(StmtMatch->Result)),
              IsSomething(Eq("foo")));
  EXPECT_THAT(Stencil.addedIncludes(), testing::IsEmpty());
  EXPECT_THAT(Stencil.removedIncludes(),
              testing::UnorderedElementsAre("include/me.h"));
}

using stencil_generators::apply;

TEST(StencilEqualityTest, Equality) {
  using stencil_generators::dPrint;
  auto Lhs = Stencil::cat(addInclude("foo/bar.h"), removeInclude("bar/baz.h"),
                          "foo", node("node"), member("node", text("bar")),
                          asValue("value_id"), asAddress("addr_id"),
                          parens("parens_id"), name("name_id"), args("args_id"),
                          dPrint("dprint_id"));
  auto Rhs = Lhs;
  EXPECT_THAT(Lhs, Eq(Rhs));
}

TEST(StencilEqualityTest, InEqualityDifferentOrdering) {
  auto Lhs = Stencil::cat("foo", node("node"), member("node", text("bar")));
  auto Rhs = Stencil::cat(member("node", text("bar")), "foo", node("node"));
  EXPECT_THAT(Lhs, Ne(Rhs));
}

TEST(StencilEqualityTest, InEqualityDifferentSizes) {
  auto Lhs = Stencil::cat("foo", node("node"), member("node", text("bar")));
  auto Rhs = Stencil::cat(removeInclude("foo/bar.h"), "foo", node("node"),
                          member("node", text("bar")));
  EXPECT_THAT(Lhs, Ne(Rhs));
}

TEST(StencilEqualityTest, InEqualityDifferentExpOp) {
  auto Lhs = Stencil::cat(asValue("id"));
  auto Rhs = Stencil::cat(asAddress("id"));
  EXPECT_THAT(Lhs, Ne(Rhs));
}

TEST(StencilEqualityTest, InEqualityDifferentMemberParts) {
  auto Lhs = Stencil::cat(member("id", node("bar")));
  auto Rhs = Stencil::cat(member("id", text("foo")));
  EXPECT_THAT(Lhs, Ne(Rhs));
}

TEST(StencilEqualityTest, NodeFunctionOpNotComparable) {
  auto SimpleFn = [](const clang::ast_type_traits::DynTypedNode &Node,
                     const clang::ASTContext &Context) {
    return fixit::getText(Node, Context).str();
  };
  auto Lhs = Stencil::cat(apply(SimpleFn, "id0"));
  auto Rhs = Stencil::cat(apply(SimpleFn, "id0"));
  EXPECT_THAT(Lhs, Ne(Rhs));
}

TEST(StencilEqualityTest, StringFunctionOp) {
  auto SimpleFn = [](llvm::StringRef S) { return (S + " - 3").str(); };
  auto Lhs = Stencil::cat(apply(SimpleFn, "id0"));
  auto Rhs = Stencil::cat(apply(SimpleFn, "id0"));
  EXPECT_THAT(Lhs, Ne(Rhs));
}
}  // namespace
}  // namespace tooling
}  // namespace clang
