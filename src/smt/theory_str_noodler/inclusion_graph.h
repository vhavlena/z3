
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include "inclusion_graph_node.h"

namespace smt::noodler {
    class Graph {
    public:
        using TargetNodes = std::unordered_set<GraphNode*>;
        using Edges = std::unordered_map<GraphNode*, TargetNodes>;

        Graph() = default;

        std::set<GraphNode> nodes;
        std::unordered_map<GraphNode*, std::unordered_set<GraphNode*>> edges;

        void add_edge(GraphNode* source, GraphNode* target) {
            edges[source].insert(target);
        }

        size_t get_num_of_edges() {
            size_t num_of_edges{ 0 };
            for (const auto& edge_set: edges) {
                num_of_edges += edge_set.second.size();
            }
            return num_of_edges;
        }

        const Edges& get_edges() const { return edges; }

        std::optional<const std::reference_wrapper<TargetNodes>> get_edges(const GraphNode* const source) {
            const auto source_edges{ edges.find(const_cast<GraphNode*>(source)) };
            if (source_edges != edges.end()) {
                return std::make_optional<const std::reference_wrapper<TargetNodes>>(source_edges->second);
            }
            return std::nullopt;
        }

        // TODO: Method to get edges from node.
    }; // Class Graph.

    class Formula {
    public:
        Formula(): predicates() {}

        std::unordered_set<Predicate, Predicate::HashFunction>& get_predicates() { return predicates; }
        const std::unordered_set<Predicate, Predicate::HashFunction>& get_predicates() const { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(const Predicate& predicate) { predicates.insert(predicate); }

    private:
        std::unordered_set<Predicate, Predicate::HashFunction> predicates;
    }; // Class Formula.

    Graph create_inclusion_graph(const Formula& predicates);

    Graph create_simplified_splitting_graph(const Formula& formula);

    Graph create_inclusion_graph(const Graph& simplified_splitting_graph);
}


#endif //Z3_INCLUSION_GRAPH_H
