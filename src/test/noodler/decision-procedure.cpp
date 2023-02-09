#include <iostream>
#include <algorithm>

#include <catch2/catch_test_macros.hpp>
#include <mata/re2parser.hh>
#include <utility>
#include <smt/theory_str_noodler/decision_procedure.h>
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"

using namespace smt::noodler;

class TheoryStrNoodlerCUT : public theory_str_noodler {
public:
    TheoryStrNoodlerCUT(smt::context &ctx, ast_manager &m, const theory_str_params &params)
            : theory_str_noodler(ctx, m, params) {}

    using theory_str_noodler::m_util_s, theory_str_noodler::m, theory_str_noodler::m_util_a;
};

class DecisionProcedureCUT : public DecisionProcedure {
public:
    DecisionProcedureCUT(const Formula &equalities, AutAssignment init_aut_ass,
                         const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                         ast_manager& m, seq_util& m_util_s, arith_util& m_util_a
    ) : DecisionProcedure(equalities, std::move(init_aut_ass), init_length_sensitive_vars, m, m_util_s, m_util_a) {}

    using DecisionProcedure::compute_next_solution;
    using DecisionProcedure::get_lengths;
    using DecisionProcedure::preprocess;
    using DecisionProcedure::solution;
};

// variables have one char names
Predicate create_equality(std::string left_side, std::string right_side) {
    std::vector<BasicTerm> left_side_vars;
    for (char var_name : left_side) {
        left_side_vars.push_back(BasicTerm(BasicTermType::Variable, std::string(1, var_name)));
    }
    std::vector<BasicTerm> right_side_vars;
    for (char var_name : right_side) {
        right_side_vars.push_back(BasicTerm(BasicTermType::Variable, std::string(1, var_name)));
    }
    return Predicate(PredicateType::Equation, { left_side_vars, right_side_vars});
}

BasicTerm get_var(char var) {
    return BasicTerm(BasicTermType::Variable, std::string(1, var));
}

static std::shared_ptr<Mata::Nfa::Nfa> regex_to_nfa(const std::string& regex) {
    Mata::Nfa::Nfa aut;
    Mata::RE2Parser::create_nfa(&aut, regex);
    return std::make_shared<Mata::Nfa::Nfa>(aut);
}

static std::map<BasicTerm, expr_ref> create_var_map(const std::unordered_set<BasicTerm>& vars, ast_manager& m, seq_util& m_util_s) {
    std::map<BasicTerm, expr_ref> ret;
    
    for(const BasicTerm& v : vars) {
        expr_ref var(m_util_s.mk_skolem(symbol(v.get_name()), 0, nullptr, m_util_s.mk_string_sort()), m);
        ret.insert({v, var});
    }

    return ret;
}

TEST_CASE("Decision Procedure", "[noodler]") {
    memory::initialize(0);
    smt_params params;
    ast_manager ast_m;
    reg_decl_plugins(ast_m);
    smt::context ctx{ast_m, params };
    theory_str_params str_params{};
    TheoryStrNoodlerCUT noodler{ctx, ast_m, str_params };
    auto& m_util_s{ noodler.m_util_s };
    auto& m_util_a{ noodler.m_util_a };
    auto& m{ noodler.m };

    SECTION("unsat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-simple", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(proc.compute_next_solution()); 
    }

    SECTION("unsat-FM-example", "[noodler]") {

        Formula equalities;
        equalities.add_predicate(create_equality("zyx", "xxz"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a+b+");
        init_ass[get_var('z')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("unsat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-simple-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a);
        CHECK(proc.compute_next_solution());
        CHECK(proc.compute_next_solution());
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-simple-length-substitution", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a);

        REQUIRE(proc.compute_next_solution());

        REQUIRE(proc.solution.substitution_map.count(get_var('z')) > 0);
        const auto &z_subst = proc.solution.substitution_map.at(get_var('z'));
        CHECK(z_subst.size() == 1);
        const auto &z_tmp_var = z_subst[0];
        REQUIRE(proc.solution.substitution_map.count(get_var('x')) > 0);
        REQUIRE(proc.solution.substitution_map.at(get_var('x')).size() == 1);
        CHECK(z_tmp_var == proc.solution.substitution_map.at(get_var('x'))[0]);
        REQUIRE(proc.solution.aut_ass.count(z_tmp_var) > 0);
        CHECK(Mata::Nfa::are_equivalent(*(proc.solution.aut_ass.at(z_subst[0])), *regex_to_nfa("a")));

        CHECK(proc.solution.substitution_map.count(get_var('u')) + proc.solution.substitution_map.count(get_var('y')) == 1);
        CHECK(proc.solution.aut_ass.count(get_var('u')) + proc.solution.aut_ass.count(get_var('y')) == 1);

        CHECK(!proc.compute_next_solution());
    }

    SECTION("unsat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-two-equations", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("a*");
        init_ass[get_var('z')] = regex_to_nfa("a*");
        init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('r')] = regex_to_nfa("aaa");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(proc.compute_next_solution());
    }

    SECTION("unsat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
        init_ass[get_var('z')] = regex_to_nfa("b");
        init_ass[get_var('u')] = regex_to_nfa("b*");
        init_ass[get_var('r')] = regex_to_nfa("a*");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-two-equations-length", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") }, m, m_util_s, m_util_a);

        REQUIRE(proc.compute_next_solution());

        AutAssignment squashed_aut_ass = proc.solution.flatten_substition_map();
        CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('x')), *regex_to_nfa("a")));
        CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('z')), *regex_to_nfa("a")));

        auto l_vars = { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") };
        auto var_map = create_var_map(l_vars, m, m_util_s);
        expr_ref len = proc.get_lengths(var_map);
        expr_ref res(m.mk_and(  
            m.mk_and(
                m.mk_true(),
                m.mk_or(
                    m.mk_false(), 
                    m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, "x"))), m_util_a.mk_int(1)))
            ),  
            m.mk_or(m.mk_false(), 
            m.mk_eq(m_util_s.str.mk_length(var_map.at(BasicTerm(BasicTermType::Variable, "z"))), m_util_a.mk_int(1))) ), 
        m);

        CHECK(len->hash() == res->hash());
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-two-equations-length2", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("xy", "zu"));
        equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*");
        init_ass[get_var('y')] = regex_to_nfa("ab*");
        init_ass[get_var('z')] = regex_to_nfa("ab*");
        init_ass[get_var('u')] = regex_to_nfa("a*");
        init_ass[get_var('r')] = regex_to_nfa("ab*a");
        DecisionProcedureCUT proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") , BasicTerm(BasicTermType::Variable, "r") }, m, m_util_s, m_util_a);

        REQUIRE(proc.compute_next_solution());

        AutAssignment squashed_aut_ass = proc.solution.flatten_substition_map();
        CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('x')), *regex_to_nfa("a")));
        CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('z')), *regex_to_nfa("a")));
        CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('r')), *regex_to_nfa("aa")));

        CHECK(!proc.compute_next_solution());
    }

    SECTION("unsat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("aa?b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(!proc.compute_next_solution());
    }

    SECTION("sat-simple-non-chain-free", "[nooodler]") {
        Formula equalities;
        equalities.add_predicate(create_equality("x", "xx"));
        // equalities.add_predicate(create_equality("yx", "r"));
        AutAssignment init_ass;
        init_ass[get_var('x')] = regex_to_nfa("a*b*");
        DecisionProcedureCUT proc(equalities, init_ass, { }, m, m_util_s, m_util_a);
        CHECK(proc.compute_next_solution());
    }
}
