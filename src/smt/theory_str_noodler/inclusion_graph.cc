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

Graph smt::noodler::create_inclusion_graph(const Formula& formula) {
    // Assert block.
    {
        const auto &predicates{formula.get_predicates()};
        for (const auto &predicate: formula.get_predicates()) {
            assert(predicate.get_left_side() != predicate.get_right_side() &&
                   "Two equal sides in one equation should never appear here in our algorithm"
            );
        }

        for (auto iter{predicates.begin()}; iter != predicates.end(); ++iter) {
            auto next_iter{iter};
            next_iter++;
            for (; next_iter != predicates.end(); ++next_iter) {
                assert(*iter != *next_iter && "Two equal equations should never appear here in our algorithm");
            }

        }
    }

    Graph splitting_graph{ create_simplified_splitting_graph(formula) };
    return create_inclusion_graph(std::move(splitting_graph));;
}

Graph smt::noodler::create_simplified_splitting_graph(const Formula& formula) {
    Graph graph;

    // Add all nodes which are not already present in direct and switched form.
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
            auto& source_right_side{ source_predicate.get_right_side() };
            auto& target_left_side{ target_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (!have_same_var(source_left_side, target_right_side)) {
                continue;
            } else if (source_left_side == target_right_side) {
                // Have same var and sides are equal.

                if (source_right_side == target_left_side) { // In the same equation.
                    if (!source_predicate.mult_occurr_var_side(Predicate::EquationSideType::Left)) {
                        // Does not have multiple occurrences of one var. Hence, cannot have an edge.
                        continue;
                    }
                } else {
                    // In different equation.
                }

            } else {
                // Have same var and sides are not equal, automatically add a new edge.
            }

            graph.add_edge(const_cast<GraphNode*>(&source_node), const_cast<GraphNode*>(&target_node));
        }
    }

    return graph;
}

Graph smt::noodler::create_inclusion_graph(Graph simplified_splitting_graph) {
    Graph inclusion_graph{};

    bool splitting_graph_changed{ true };
    while(splitting_graph_changed) {
        splitting_graph_changed = false;

        for (auto& const_node: simplified_splitting_graph.nodes) {
            auto node{ const_cast<GraphNode *>(&const_node) };
            if (simplified_splitting_graph.get_edges_to(node).empty()) {
                inclusion_graph.nodes.insert(*node);
                splitting_graph_changed = true;

                auto switched_node{ simplified_splitting_graph.get_node(node->get_predicate().get_switched_sides_predicate()) };

                // Remove edges of node and switched node.
                simplified_splitting_graph.remove_edges_with(node);
                simplified_splitting_graph.remove_edges_with(switched_node);

                simplified_splitting_graph.nodes.erase(*node);
                simplified_splitting_graph.nodes.erase(*switched_node);
            }
        }
    }
    inclusion_graph.nodes.merge(simplified_splitting_graph.nodes);

    for (const GraphNode& source_node: inclusion_graph.nodes ) {
        for (const GraphNode& target_node: inclusion_graph.nodes) {
            auto& source_predicate{ source_node.get_predicate() };
            auto& target_predicate{ target_node.get_predicate() };
            auto& source_left_side{ source_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (!have_same_var(source_left_side, target_right_side)) {
                continue;
            }

            // Have same var, automatically add a new edge.
            inclusion_graph.add_edge(const_cast<GraphNode*>(&source_node), const_cast<GraphNode*>(&target_node));
        }
    }

    return inclusion_graph;
}
