#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>

using namespace smt::noodler;

TEST_CASE( "Inclusion graph node", "[noodler]" ) {
    auto predicate{ Predicate(PredicateType::Equation) };
    CHECK(predicate.get_type() == PredicateType::Equation);

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(term_name, BasicTermType::Variable) };
    CHECK(term.get_name() == term_name);
}
