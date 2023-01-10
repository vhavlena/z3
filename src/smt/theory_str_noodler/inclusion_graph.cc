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

Graph smt::noodler::Graph::deep_copy() const {
    Graph new_graph;
    std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> this_to_new_node;

    for (const auto &this_node : get_nodes()) {
        this_to_new_node[this_node] = new_graph.add_node(this_node->get_predicate());
    }

    for (const auto &edge : get_edges()) {
        const auto &source = edge.first;
        for (const auto &target : edge.second) {
            new_graph.add_edge(this_to_new_node[source], this_to_new_node[target]);
        }
    }

    return new_graph;
}

Graph smt::noodler::Graph::create_inclusion_graph(const Formula& formula) {
    // Assert block.
    {
        const auto &predicates{formula.get_predicates()};
        for (const auto &predicate: formula.get_predicates()) {
            assert(predicate.get_left_side() != predicate.get_right_side() &&
                   "Two equal sides in one equation should never appear here in our algorithm"
            );
        }

        for (auto predicate_iter{predicates.begin()}; predicate_iter != predicates.end(); ++predicate_iter) {
            auto next_predicate_iter{predicate_iter};
            next_predicate_iter++;
            for (; next_predicate_iter != predicates.end(); ++next_predicate_iter) {
                assert(*predicate_iter != *next_predicate_iter && "Two equal equations should never appear here in our algorithm");
            }

        }
    }

    Graph splitting_graph{ create_simplified_splitting_graph(formula) };
    return create_inclusion_graph(splitting_graph);
}

Graph smt::noodler::Graph::create_simplified_splitting_graph(const Formula& formula) {
    Graph graph;

    // Add all nodes which are not already present in direct and switched form.
    for (const auto& predicate: formula.get_predicates()) {
        graph.add_node(predicate);
        graph.add_node(predicate.get_switched_sides_predicate());
    }

    if (graph.nodes.empty()) {
        return Graph{};
    }

    for (auto &source_node: graph.get_nodes() ) {
        for (auto &target_node: graph.get_nodes()) {
            auto& source_predicate{ source_node->get_predicate() };
            auto& target_predicate{ target_node->get_predicate() };
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

            graph.add_edge(source_node, target_node);
        }
    }

    for (auto& node: graph.get_nodes()) {
        // auto node{ const_cast<GraphNode *>(&const_node) };
        if (graph.get_edges_to(node).empty()) {
            graph.initial_nodes.insert(node);
        }
    }

    return graph;
}

Graph smt::noodler::Graph::create_inclusion_graph(Graph& simplified_splitting_graph) {
    Graph inclusion_graph{};

    bool splitting_graph_changed{ true };
    while(splitting_graph_changed) {
        splitting_graph_changed = false;

        for (auto& node: simplified_splitting_graph.get_nodes()) {
            if (simplified_splitting_graph.get_edges_to(node).empty()) {
                inclusion_graph.nodes.insert(node);
                inclusion_graph.nodes_not_on_cycle.insert(node); // the inserted node cannot be on the cycle, because it is either initial or all nodes leading to it were not on cycle
                if (simplified_splitting_graph.initial_nodes.count(node) > 0) {
                    inclusion_graph.initial_nodes.insert(node);
                } 

                auto switched_node{ simplified_splitting_graph.get_node(node->get_predicate().get_switched_sides_predicate()) };

                // Remove edges of node and switched node.
                simplified_splitting_graph.remove_edges_with(node);
                simplified_splitting_graph.remove_edges_with(switched_node);

                simplified_splitting_graph.nodes.erase(node);
                simplified_splitting_graph.nodes.erase(switched_node);

                splitting_graph_changed = true;
                break;
            }
        }
    }

    // we add rest of the nodes (the ones on the cycle) to the inclusion graph and make them initial
    for (auto& node: simplified_splitting_graph.get_nodes()) {
        inclusion_graph.initial_nodes.insert(node);
    }
    inclusion_graph.nodes.merge(simplified_splitting_graph.nodes);

    for (auto& source_node: inclusion_graph.get_nodes() ) {
        for (auto& target_node: inclusion_graph.get_nodes()) {
            auto& source_predicate{ source_node->get_predicate() };
            auto& target_predicate{ target_node->get_predicate() };
            auto& source_left_side{ source_predicate.get_left_side() };
            auto& target_right_side{ target_predicate.get_right_side() };

            if (have_same_var(source_left_side, target_right_side)) {
                // Have same var, automatically add a new edge.
                inclusion_graph.add_edge(source_node, target_node);
            }
        }
    }

    return inclusion_graph;
}
