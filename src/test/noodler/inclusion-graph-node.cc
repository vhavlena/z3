#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>

using namespace smt::noodler;

TEST_CASE( "Inclusion graph node", "[noodler]" ) {
    auto predicate{ Predicate(PredicateType::Equation) };
    CHECK(predicate.get_type() == PredicateType::Equation);

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(BasicTermType::Variable, term_name) };
    CHECK(term.get_name() == term_name);

    auto& left{ predicate.get_left() };
    left.emplace_back(term);
    left.emplace_back(term);
    CHECK(predicate.multiple_occurrence_of_term_on_side(Predicate::EquationSideType::Left));
}
