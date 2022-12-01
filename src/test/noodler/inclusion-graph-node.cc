#include <iostream>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa.hh>

#include <smt/theory_str_noodler/inclusion_graph_node.h>
#include "smt/theory_str_noodler/inclusion_graph.h"

using namespace smt::noodler;

TEST_CASE( "Inclusion graph node", "[noodler]" ) {
    auto predicate{ Predicate(PredicateType::Equation) };
    auto predicate_ineq{ Predicate(PredicateType::Inequation) };
    CHECK(predicate.get_type() == PredicateType::Equation);

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(BasicTermType::Variable, term_name) };
    CHECK(term.get_name() == term_name);

    auto& left{ predicate.get_left_side() };
    left.emplace_back(term);
    left.emplace_back( BasicTermType::Literal, "lit" );
    left.emplace_back(term);
    CHECK(predicate.mult_occurr_var_side(Predicate::EquationSideType::Left));

    auto& left_alt{ predicate.get_side(Predicate::EquationSideType::Left) };
    CHECK(left == left_alt);

    CHECK(predicate.is_eq_or_ineq());
    CHECK(predicate.get_side_vars(Predicate::EquationSideType::Left) == std::set<BasicTerm>{ term });
    CHECK(predicate.get_side_vars(Predicate::EquationSideType::Right).empty());

    CHECK(predicate != predicate_ineq);

    BasicTerm term_lit{ BasicTermType::Literal, "3"};
    BasicTerm term_lit2{ BasicTermType::Literal, "5"};
    BasicTerm term_var{ BasicTermType::Variable, "4"};
    BasicTerm term_var2{ BasicTermType::Variable, "6"};
    CHECK(term_lit < term_lit2);
    CHECK(term_lit2 > term_lit);
    CHECK(term_var < term_lit2);
    CHECK(term_var < term_lit);
    CHECK(term_var < term_var2);
    CHECK(term_var2 > term_var);
    CHECK(term_var == term_var);
    CHECK(term_var2 < term_lit);
    CHECK(term_var2 < term_lit2);
    CHECK(term != term_var);
}

TEST_CASE("Conversion to strings", "[noodler]") {
    CHECK(smt::noodler::to_string(BasicTermType::Literal) == "Literal");
    CHECK(smt::noodler::to_string(BasicTermType::Variable) == "Variable");
    CHECK(BasicTerm{ BasicTermType::Literal }.to_string().empty());
    CHECK(BasicTerm{ BasicTermType::Literal, "4" }.to_string() == "\"4\"");
    CHECK(BasicTerm{ BasicTermType::Variable, "x_42" }.to_string() == "x_42");

    auto pred{ Predicate{ PredicateType::Equation, {
        { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
        { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred.to_string() == "Equation: \"4\" x_42 = xyz y_58");

    auto pred_ineq{ Predicate{ PredicateType::Inequation, {
            { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
            { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred_ineq.to_string() == "Inequation: \"4\" x_42 != xyz y_58");

    CHECK(pred_ineq.get_vars() == std::set{
          BasicTerm{ BasicTermType::Variable, "x_42" },
          BasicTerm{ BasicTermType::Variable, "xyz" },
          BasicTerm{ BasicTermType::Variable, "y_58" }
    } );
}

TEST_CASE("Mata integration") {
    auto nfa = Mata::Nfa::Nfa(3);
    nfa.initial_states = { 0, 1};
    nfa.final_states = { 3, 1};
    nfa.add_trans(0, 42, 1);
    nfa.add_trans(1, 42, 2);
    CHECK(nfa.has_final(1));
    CHECK(!nfa.has_final(0));
    CHECK(nfa.has_trans(0, 42, 1));
    CHECK(!nfa.has_trans(1, 42, 1));
    CHECK(!nfa.has_no_transitions());
}

TEST_CASE("Splitting graph", "[noodler]") {
    Graph graph;

    SECTION("yx=xy") {
        BasicTerm x{ BasicTermType::Variable, "x" };
        BasicTerm y{ BasicTermType::Variable, "y" };
        Predicate predicate{ PredicateType::Equation, { { x, y }, {y, x} } };
        CHECK(predicate.to_string() == "Equation: x y = y x");

        Formula formula;
        formula.add_predicate(predicate);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{ GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() } });
        REQUIRE(graph.edges.size() == 2);
        CHECK(graph.edges.begin()->first->get_predicate().to_string() == predicate.get_switched_sides_predicate().to_string());
        CHECK(graph.edges.begin()->first == *graph.edges.begin()->second.begin());
        CHECK((++graph.edges.begin())->first->get_predicate().to_string() == predicate.to_string());
        CHECK((++graph.edges.begin())->first == *(++graph.edges.begin())->second.begin());

    }
}
