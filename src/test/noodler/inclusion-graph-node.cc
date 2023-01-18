#include <iostream>

#include <catch2/catch_test_macros.hpp>
#include <mata/nfa.hh>

#include <smt/theory_str_noodler/inclusion_graph_node.h>
#include "smt/theory_str_noodler/inclusion_graph.h"

using namespace smt::noodler;

TEST_CASE("Graph::get_edges()", "[noodler]") {
    Graph graph;
    Formula formula;
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
    Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };
    formula.add_predicate(predicate);
    formula.add_predicate(predicate2);
    graph = create_simplified_splitting_graph(formula);

    auto edges{ graph.get_edges(&(*graph.nodes.begin())) };
    REQUIRE(edges.has_value());
    CHECK((*edges.value().get().begin())->get_predicate().to_string() == "Equation: y x = x y");
}

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

TEST_CASE("Mata integration", "[noodler]") {
    auto nfa = Mata::Nfa::Nfa(3);
    nfa.initial = { 0, 1};
    nfa.final = { 3, 1};
    nfa.delta.add(0, 42, 1);
    nfa.delta.add(1, 42, 2);
    CHECK(nfa.final[1]);
    CHECK(!nfa.final[0]);
    CHECK(nfa.delta.contains(0, 42, 1));
    CHECK(!nfa.delta.contains(1, 42, 1));
    CHECK(!nfa.delta.empty());
}

TEST_CASE("Graph::get_edges_to", "[noodler]") {
    Graph graph;
    Formula formula;
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
    Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

    formula.add_predicate(predicate);
    formula.add_predicate(predicate2);
    graph = create_simplified_splitting_graph(formula);
    auto target{ graph.get_node(predicate) };
    auto edges_to_target{ graph.get_edges_to(target) };
    CHECK(edges_to_target.find(graph.get_node(predicate)) != edges_to_target.end());
    CHECK(edges_to_target.find(graph.get_node(predicate2)) != edges_to_target.end());
    CHECK(edges_to_target.find(graph.get_node(predicate2.get_switched_sides_predicate())) != edges_to_target.end());
}

TEST_CASE("Inclusion graph", "[noodler]") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };
    BasicTerm z{ BasicTermType::Variable, "z" };

    SECTION("u = z && v = u && x = uvx") {
        Predicate predicate{ PredicateType::Equation, { { u }, { z } } };
        Predicate predicate2{ PredicateType::Equation, { { v }, { u } } };
        Predicate predicate3{ PredicateType::Equation, { { x }, { u, v, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        formula.add_predicate(predicate3);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes.size() == 5);
        CHECK(graph.edges.size() == 5);
        CHECK(graph.get_num_of_edges() == 12);
    }

    SECTION("x = xy && xy = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
        Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 4);
        CHECK(graph.get_num_of_edges() == 16);
    }

    SECTION("yx = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };

        formula.add_predicate(predicate);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 2);
        CHECK(graph.get_num_of_edges() == 4);
    }

    SECTION("x = xy") {
        Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };

        formula.add_predicate(predicate);
        //CHECK_THROWS(create_inclusion_graph(formula)); // FIXME: Catch2 cannot catch failing assert.
    }

    SECTION("x=y && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate },
                GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.empty());
    }

    SECTION("x=yx && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 3);
        CHECK(graph.get_num_of_edges() == 6);
    }

    SECTION("x=y && u = v") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { v } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_inclusion_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate },
                GraphNode{ predicate2 },
        });
        CHECK(graph.nodes.size() == 2);
        CHECK(graph.edges.empty());
    }
}

TEST_CASE("Splitting graph", "[noodler]") {
    Graph graph;
    Formula formula;

    BasicTerm u{ BasicTermType::Variable, "u" };
    BasicTerm v{ BasicTermType::Variable, "v" };
    BasicTerm x{ BasicTermType::Variable, "x" };
    BasicTerm y{ BasicTermType::Variable, "y" };

    SECTION("yx=xy") {
        Predicate predicate{ PredicateType::Equation, { { x, y }, {y, x} } };
        CHECK(predicate.to_string() == "Equation: x y = y x");

        formula.add_predicate(predicate);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{ GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() } });
        REQUIRE(graph.edges.size() == 2);
        CHECK(graph.edges.begin()->first->get_predicate().to_string() == predicate.get_switched_sides_predicate().to_string());
        CHECK(graph.edges.begin()->first == *graph.edges.begin()->second.begin());
        CHECK((++graph.edges.begin())->first->get_predicate().to_string() == predicate.to_string());
        CHECK((++graph.edges.begin())->first == *(++graph.edges.begin())->second.begin());
    }

    SECTION("yx=yx") {
        Predicate predicate{ PredicateType::Equation, { { y, x }, {y, x} } };
        CHECK(predicate.to_string() == "Equation: y x = y x");

        formula.add_predicate(predicate);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{ GraphNode{ predicate } });
        REQUIRE(graph.edges.empty());
    }

    SECTION("xx=xx") {
        Predicate predicate{ PredicateType::Equation, { { x, x }, {x, x} } };
        CHECK(predicate.to_string() == "Equation: x x = x x");

        formula.add_predicate(predicate);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{ GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() } });
        REQUIRE(graph.edges.size() == 1);
        CHECK(graph.edges.begin()->first->get_predicate().to_string() == predicate.to_string());
        CHECK(graph.edges.begin()->first == *graph.edges.begin()->second.begin());
    }

    SECTION("x=xy") {
        Predicate predicate{ PredicateType::Equation, { { x }, {x, y} } };
        CHECK(predicate.to_string() == "Equation: x = x y");

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

    SECTION("x=xy && xy = yx") {
        Predicate predicate{ PredicateType::Equation, { { x }, { x, y } } };
        Predicate predicate2{ PredicateType::Equation, { { x, y }, { y, x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
            GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
            GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 4);
        CHECK(graph.get_num_of_edges() == 12);
    }

    SECTION("x=y && x = u") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { x }, { u } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 2);
        CHECK(graph.get_num_of_edges() == 2);
    }

    SECTION("x=yx && u = x") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y, x } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { x } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.size() == 3);
        CHECK(graph.get_num_of_edges() == 6);
    }

    SECTION("x=y && u = v") {
        Predicate predicate{ PredicateType::Equation, { { x }, { y } } };
        Predicate predicate2{ PredicateType::Equation, { { u }, { v } } };

        formula.add_predicate(predicate);
        formula.add_predicate(predicate2);
        graph = create_simplified_splitting_graph(formula);
        CHECK(graph.nodes == std::set<GraphNode>{
                GraphNode{ predicate }, GraphNode{ predicate.get_switched_sides_predicate() },
                GraphNode{ predicate2 }, GraphNode{ predicate2.get_switched_sides_predicate() },
        });
        CHECK(graph.edges.empty());
    }
}
