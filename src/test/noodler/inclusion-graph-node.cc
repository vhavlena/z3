#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>

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
