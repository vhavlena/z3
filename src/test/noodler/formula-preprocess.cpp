#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>
#include <smt/theory_str_noodler/formula_preprocess.h>
#include <smt/theory_str_noodler/theory_str_noodler.h>

using namespace smt::noodler;

TEST_CASE( "Preprocess to strings", "[noodler]" ) {
    auto predicate1{ Predicate(PredicateType::Equation) };

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(BasicTermType::Variable, term_name) };
    auto& left{ predicate1.get_left_side() };
    left.emplace_back(term);
    left.emplace_back( BasicTermType::Literal, "lit" );
    left.emplace_back(term);

    auto term2{ BasicTerm(BasicTermType::Variable, "x_2") };
    auto& right{ predicate1.get_right_side() };
    right.emplace_back(term2);
    right.emplace_back(term2);

    BasicTerm term_lit{ BasicTermType::Literal, "3"};
    BasicTerm term_lit2{ BasicTermType::Literal, "5"};
    BasicTerm term_var{ BasicTermType::Variable, "x_4"};
    BasicTerm term_var2{ BasicTermType::Variable, "x_6"};

    Predicate predicate2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({term_lit, term_var}), std::vector<BasicTerm>({term_lit2, term_var2}) })  );

    INFO(predicate1.to_string());
    INFO(predicate2.to_string());

    Formula conj;
    conj.add_predicate(predicate1);
    conj.add_predicate(predicate2);
    FormulaVar fvar(conj);
    INFO(fvar.to_string());

    CHECK(false);
}