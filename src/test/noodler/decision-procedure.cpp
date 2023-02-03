#include <iostream>
#include <algorithm>

#include <catch2/catch_test_macros.hpp>
#include <mata/re2parser.hh>
#include <smt/theory_str_noodler/decision_procedure.h>

using namespace smt::noodler;


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

TEST_CASE("unsat-simple", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a");
    init_ass[get_var('y')] = regex_to_nfa("a*");
    init_ass[get_var('z')] = regex_to_nfa("b");
    init_ass[get_var('u')] = regex_to_nfa("b*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-simple", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("a*");
    init_ass[get_var('z')] = regex_to_nfa("a*");
    init_ass[get_var('u')] = regex_to_nfa("a*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(proc.compute_next_solution());
}

TEST_CASE("unsat-FM-example", "[noodler]") {
    
    Formula equalities;
    equalities.add_predicate(create_equality("zyx", "xxz"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("a+b+");
    init_ass[get_var('z')] = regex_to_nfa("b*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("unsat-simple-length", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a");
    init_ass[get_var('y')] = regex_to_nfa("a*");
    init_ass[get_var('z')] = regex_to_nfa("b");
    init_ass[get_var('u')] = regex_to_nfa("b*");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-simple-length", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("a*");
    init_ass[get_var('z')] = regex_to_nfa("a*");
    init_ass[get_var('u')] = regex_to_nfa("a*");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") });
    CHECK(proc.compute_next_solution());
    CHECK(proc.compute_next_solution());
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-simple-length-substitution", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a");
    init_ass[get_var('y')] = regex_to_nfa("ab*");
    init_ass[get_var('z')] = regex_to_nfa("ab*");
    init_ass[get_var('u')] = regex_to_nfa("a*");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") });

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

TEST_CASE("unsat-two-equations", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
    init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
    init_ass[get_var('z')] = regex_to_nfa("b");
    init_ass[get_var('u')] = regex_to_nfa("b*");
    init_ass[get_var('r')] = regex_to_nfa("a*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-two-equations", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("a*");
    init_ass[get_var('z')] = regex_to_nfa("a*");
    init_ass[get_var('u')] = regex_to_nfa("(a|b)*");
    init_ass[get_var('r')] = regex_to_nfa("aaa");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(proc.compute_next_solution());
}

TEST_CASE("unsat-two-equations-length", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("(a|b)*");
    init_ass[get_var('y')] = regex_to_nfa("(a|b)*");
    init_ass[get_var('z')] = regex_to_nfa("b");
    init_ass[get_var('u')] = regex_to_nfa("b*");
    init_ass[get_var('r')] = regex_to_nfa("a*");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-two-equations-length", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("ab*");
    init_ass[get_var('z')] = regex_to_nfa("ab*");
    init_ass[get_var('u')] = regex_to_nfa("a*");
    init_ass[get_var('r')] = regex_to_nfa("ab*a");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") });

    REQUIRE(proc.compute_next_solution());

    AutAssignment squashed_aut_ass = proc.solution.flatten_substition_map();
    CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('x')), *regex_to_nfa("a")));
    CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('z')), *regex_to_nfa("a")));
    
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-two-equations-length2", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("xy", "zu"));
    equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*");
    init_ass[get_var('y')] = regex_to_nfa("ab*");
    init_ass[get_var('z')] = regex_to_nfa("ab*");
    init_ass[get_var('u')] = regex_to_nfa("a*");
    init_ass[get_var('r')] = regex_to_nfa("ab*a");
    DecisionProcedure proc(equalities, init_ass, { BasicTerm(BasicTermType::Variable, "x"), BasicTerm(BasicTermType::Variable, "z") , BasicTerm(BasicTermType::Variable, "r") });

    REQUIRE(proc.compute_next_solution());

    AutAssignment squashed_aut_ass = proc.solution.flatten_substition_map();
    CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('x')), *regex_to_nfa("a")));
    CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('z')), *regex_to_nfa("a")));
    CHECK(Mata::Nfa::are_equivalent(*squashed_aut_ass.at(get_var('r')), *regex_to_nfa("aa")));

    CHECK(!proc.compute_next_solution());
}

TEST_CASE("unsat-simple-non-chain-free", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("x", "xx"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("aa?b*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(!proc.compute_next_solution());
}

TEST_CASE("sat-simple-non-chain-free", "[nooodler]") {
    Formula equalities;
    equalities.add_predicate(create_equality("x", "xx"));
    // equalities.add_predicate(create_equality("yx", "r"));
    AutAssignment init_ass;
    init_ass[get_var('x')] = regex_to_nfa("a*b*");
    DecisionProcedure proc(equalities, init_ass, { });
    CHECK(proc.compute_next_solution());
}