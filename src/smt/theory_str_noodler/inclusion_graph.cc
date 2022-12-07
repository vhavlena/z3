#include "inclusion_graph.h"

namespace {
    using namespace smt::noodler;

    bool have_same_var(const std::vector<BasicTerm>& first_side, const std::vector<BasicTerm>& second_side) {
        for (const auto& first_side_term: first_side) {
            for (const auto& second_side_term: second_side) {
                if (first_side_term == second_side_term) {
                    if (first_side_term.is_variable()) {
                        return true;
                    }
                }
            }
        }
        return false;
    }
} // Anonymous namespace.

Graph smt::noodler::create_inclusion_graph(const Formula& predicates) {
    Graph splitting_graph{ create_simplified_splitting_graph(predicates) };

    // TODO: Create inclusion graph from splitting graph.

    return splitting_graph;
}

Graph smt::noodler::create_simplified_splitting_graph(const Formula& formula) {
    Graph graph;


    // TODO: Add asssert taht two equal equations are fail.

    for (const auto& predicate: formula.get_predicates()) {
        if (graph.nodes.find(GraphNode{ predicate }) == graph.nodes.end()) {
            graph.nodes.emplace(predicate);
        }

        const Predicate switched_predicate{ predicate.get_switched_sides_predicate() };
        if (graph.nodes.find(GraphNode{ switched_predicate }) == graph.nodes.end()) {
            graph.nodes.emplace(switched_predicate);
        }
    }

    if (graph.nodes.empty()) {
        return Graph{};
    }

    for (const GraphNode& source_node: graph.nodes ) {
        for (const GraphNode& target_node: graph.nodes) {
            auto& source_predicate{ source_node.get_predicate() };
            auto& target_predicate{ target_node.get_predicate() };
            auto& source_left_side{ source_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (!have_same_var(source_left_side, target_right_side)) {
                continue;
            } else if (source_left_side == target_right_side) {
                // Have same var and sides are equal.

                if (!source_predicate.mult_occurr_var_side(Predicate::EquationSideType::Left)) {
                    // Does not have multiple occurrences of one var. Hence, cannot have an edge.
                    continue;
                }
            } else {
                // Have same var and sides are not equal, automatically add a new edge.
            }

            graph.add_edge(const_cast<GraphNode*>(&source_node), const_cast<GraphNode*>(&target_node));
        }
    }

    return graph;
}


Graph smt::noodler::create_inclusion_graph(const Graph &simplified_splitting_graph) {

    return {};
}
