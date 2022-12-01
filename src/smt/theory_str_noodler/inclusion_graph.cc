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

    return splitting_graph;
}

Graph smt::noodler::create_simplified_splitting_graph(const Formula& formula) {
    Graph graph;

    for (const auto& predicate: formula.get_predicates()) {
        graph.nodes.emplace(predicate);
        graph.nodes.emplace(predicate.get_switched_sides_predicate());
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

            //graph.edges.emplace(&source_node, std::unordered_set<GraphNode*>{ &target_node });

            //if (source_node != target_node) {
            //    // The CXXGraph node IDs differ. We work with different graph graph_nodes.

            //    if (source_predicate.get_switched_sides_predicate() != target_predicate) {
            //        // Nodes are not their switched variants (duals).

            //        const auto source_vars{ source_predicate.get_side_vars(Predicate::EquationSideType::Left) };
            //        const auto target_vars{ target_predicate.get_side_vars(Predicate::EquationSideType::Right) };

            //        if (source_vars.)
            //    }
            //} else {
            //    // We work with the same node (of the same CXXGraph node ID). Check whether to add self-loops.

            //
            //    if (source_left_side == target_right_side) {
            //        // Left and right side are equal. Look for the same variable in different positions.
            //
            //        if (source_predicate.mult_occurr_var_side(Predicate::EquationSideType::Left)) {
            //
            //        }
            //    } else {
            //        // Left and right sides differ. Check for same variables in different positions.

            //        for (size_t source_term_index{ 0 }; source_term_index < source_left_side.size(); ++source_term_index) {
            //            for (size_t target_term_index{ source_term_index }; target_term_index < target_predicate.get_right_side().size();
            //                 ++target_term_index) {
            //            }
            //        }
            //    }

            //}
        }
    }

    return graph;
}


Graph smt::noodler::create_inclusion_graph(const Graph &simplified_splitting_graph) {

    return {};
}
