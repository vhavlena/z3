#include <iostream>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa.hh>

#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"

using namespace smt::noodler;

class TheoryStrNoodlerCUT : public theory_str_noodler {
public:
    TheoryStrNoodlerCUT(smt::context &ctx, ast_manager &m, const theory_str_params &params)
        : theory_str_noodler(ctx, m, params) {}

    using theory_str_noodler::conv_to_regex;
    using theory_str_noodler::m_util_s, theory_str_noodler::m;
};

TEST_CASE("theory_str_noodler", "[noodler]") {
    memory::initialize(0);
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    auto& m_util_s{ noodler.m_util_s };
    auto& m{ noodler.m };

    SECTION("theory_str_noodler::conv_to_regex()") {
        auto expr_x = m_util_s.re.mk_to_re(m_util_s.str.mk_string("x"));
        auto regex{ noodler.conv_to_regex(expr_x) };
        CHECK(regex == "(x)");

        auto expr_y = m_util_s.re.mk_to_re(m_util_s.str.mk_string("y"));
        regex = noodler.conv_to_regex(expr_y);
        CHECK(regex == "(y)");

        auto expr_star{m_util_s.re.mk_star(expr_x) };
        regex = noodler.conv_to_regex(expr_star);
        CHECK(regex == "(((x))*)");

        auto expr_plus{m_util_s.re.mk_plus(expr_y) };
        regex = noodler.conv_to_regex(expr_plus);
        CHECK(regex == "(((y))+)");

        auto expr_concat{ m_util_s.re.mk_concat(expr_star, expr_plus) };
        regex = noodler.conv_to_regex(expr_concat);
        CHECK(regex == "(((((x))*))((((y))+)))");
    }
}
