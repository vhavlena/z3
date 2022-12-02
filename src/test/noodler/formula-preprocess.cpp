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

    Formula conj;
    conj.add_predicate(predicate1);
    conj.add_predicate(predicate2);
    FormulaVar fvar(conj);

    VarNode v1{.var = "x_1", .eq_index = 0, .position = -1};
    VarNode v2{.var = "x_1", .eq_index = 0, .position = -1};

    CHECK(v1 == v2);
    INFO(fvar.to_string());
    CHECK(fvar.get_var_positions(predicate1, 0) == std::set<VarNode>({ {.var = "x_1", .eq_index = 0, .position = -1 }, 
        {.var = "x_1", .eq_index = 0, .position = -3 }, 
        {.var = "x_2", .eq_index = 0, .position = 1 }, 
        {.var = "x_2", .eq_index = 0, .position = 2 } }));
}

TEST_CASE( "Remove regular", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2, x6, a}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x3, b, x4, b}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5}), std::vector<BasicTerm>({x4}) })  );

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    conj.add_predicate(eq3);
    conj.add_predicate(eq4);
    FormulaPreprocess prep(conj);
    prep.remove_regular();

    CHECK(prep.get_formula().get_predicate(0) == eq1);
}