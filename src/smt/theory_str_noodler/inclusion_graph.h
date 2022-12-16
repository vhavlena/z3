
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include "inclusion_graph_node.h"

namespace smt::noodler {
    class Graph {
    public:
        using Nodes = std::unordered_set<GraphNode*>;
        using Edges = std::unordered_map<GraphNode*, Nodes>;

        Graph() = default;

        std::set<GraphNode> nodes;
        std::unordered_map<GraphNode*, std::unordered_set<GraphNode*>> edges;

        void add_edge(GraphNode* source, GraphNode* target) {
            edges[source].insert(target);
        }

        void remove_edge(GraphNode* source, GraphNode* target) {
            auto source_edges{ edges[source] };
            source_edges.erase(target);
            if (source_edges.empty()) {
                edges.erase(source);
            }
        }

        void remove_edges_from(GraphNode* source) {
            edges.erase(source);
        }

        Nodes get_edges_to(GraphNode* target) {
            Nodes source_nodes{};
            for (auto& source_edges: edges) {
                if (source_edges.second.find(target) != source_edges.second.end()) {
                    source_nodes.insert(source_edges.first);
                }
            }
            return source_nodes;
        }

        void remove_edges_to(GraphNode* target) {
            for (auto& source: get_edges_to(target)) {
                remove_edge(source, target);
            }
        }

        void remove_edges_with(GraphNode* node) {
            remove_edges_from(node);
            remove_edges_to(node);
        }

        size_t get_num_of_edges() {
            size_t num_of_edges{ 0 };
            for (const auto& edge_set: edges) {
                num_of_edges += edge_set.second.size();
            }
            return num_of_edges;
        }

        const Edges& get_edges() const { return edges; }

        std::optional<const std::reference_wrapper<Nodes>> get_edges(const GraphNode* const source) {
            const auto source_edges{ edges.find(const_cast<GraphNode*>(source)) };
            if (source_edges != edges.end()) {
                return std::make_optional<const std::reference_wrapper<Nodes>>(source_edges->second);
            }
            return std::nullopt;
        }

        GraphNode* get_node(const Predicate& predicate) {
            auto node{ nodes.find(GraphNode{ predicate }) };
            if (node == nodes.end()) { return nullptr; }
            return const_cast<GraphNode*>(&*node);
        }
    }; // Class Graph.

    class Formula {
    public:
        Formula(): predicates() {}

        std::vector<Predicate>& get_predicates() { return predicates; }
        const std::vector<Predicate>& get_predicates() const { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(const Predicate& predicate) { predicates.push_back(predicate); }

    private:
        std::vector<Predicate> predicates;
    }; // Class Formula.

    Graph create_inclusion_graph(const Formula& formula);

    Graph create_simplified_splitting_graph(const Formula& formula);

    Graph create_inclusion_graph(Graph& simplified_splitting_graph);

}


#endif //Z3_INCLUSION_GRAPH_H
