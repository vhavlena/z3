#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>
#include <CXXGraph/CXXGraph.hpp>

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

TEST_CASE("Conversion to strings") {
    CHECK(smt::noodler::to_string(BasicTermType::Literal) == "Literal");
    CHECK(smt::noodler::to_string(BasicTermType::Variable) == "Variable");
    CHECK(BasicTerm{ BasicTermType::Literal }.to_string() == "(Literal)");
    CHECK(BasicTerm{ BasicTermType::Literal, "4" }.to_string() == "\"4\" (Literal)");
    CHECK(BasicTerm{ BasicTermType::Variable, "x_42" }.to_string() == "x_42 (Variable)");

    auto pred{ Predicate{ PredicateType::Equation, {
        { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
        { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred.to_string() == "Equation: . \"4\" (Literal) . x_42 (Variable) = . xyz (Variable) . y_58 (Variable)");

    auto pred_ineq{ Predicate{ PredicateType::Inequation, {
            { { BasicTermType::Literal, "4" }, { BasicTermType::Variable, "x_42" } } ,
            { { BasicTermType::Variable, "xyz" }, { BasicTermType::Variable, "y_58" } },
    } } };

    CHECK(pred_ineq.to_string() == "Inequation: . \"4\" (Literal) . x_42 (Variable) != . xyz (Variable) . y_58 (Variable)");
}

TEST_CASE("Integration of inclusion graph") {
    auto mtp = Predicate{ PredicateType::Equation };
    auto tmp = Predicate{ PredicateType::Equation };
    CXXGRAPH::Node<Predicate> node0("0", Predicate{ PredicateType::Equation });
    std::cout << node0.getId() << "\n";
    std::cout << node0.getData().to_string() << "\n";
    CXXGRAPH::Node<Predicate> node1("1", Predicate{ PredicateType::Equation });

    CXXGRAPH::UndirectedEdge<Predicate> edge1{ 0, node0, node1};


    CXXGRAPH::T_EdgeSet<Predicate> edgeSet;
    edgeSet.insert(&edge1);

    // Can print out the edges for debugging
    std::cout << edge1 << "\n";

    CXXGRAPH::Graph<Predicate> graph{ edgeSet };
    graph.setEdgeSet(edgeSet);
    auto res = graph.dijkstra(node0, node1);

    std::cout << "Dijkstra Result: " << res.result << "\n";
}
