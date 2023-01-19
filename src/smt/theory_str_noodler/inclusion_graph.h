
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include "formula.h"

namespace smt::noodler {

    //----------------------------------------------------------------------------------------------------------------------------------

    class GraphNode {
    public:
        GraphNode() = default;
        explicit GraphNode(const Predicate& predicate) : node_predicate(predicate) {}

        void set_predicate(const Predicate& predicate) { this->node_predicate = predicate; }
        [[nodiscard]] Predicate& get_predicate() { return node_predicate; }
        [[nodiscard]] const Predicate& get_predicate() const { return node_predicate; }

        struct HashFunction {
            size_t operator()(const GraphNode& graph_node) const {
                return Predicate::HashFunction()(graph_node.node_predicate);
            }
        };

        [[nodiscard]] bool equals(const GraphNode& other) const {
            return this->node_predicate == other.node_predicate;
        }

    private:
        Predicate node_predicate;

        // TODO: Add additional attributes such as cost, etc.
    }; // Class GraphNode.

    static bool operator==(const GraphNode& lhs, const GraphNode& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const GraphNode& lhs, const GraphNode& rhs) { return !(lhs == rhs); }
    static bool operator<(const GraphNode& lhs, const GraphNode& rhs) {
        if (lhs.get_predicate() < rhs.get_predicate()) {
            return true;
        }
        return false;
    }
    static bool operator>(const GraphNode& lhs, const GraphNode& rhs) { return !(lhs < rhs); }

    //----------------------------------------------------------------------------------------------------------------------------------

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

    Graph create_inclusion_graph(const Formula& formula);

    Graph create_simplified_splitting_graph(const Formula& formula);

    Graph create_inclusion_graph(Graph& simplified_splitting_graph);

}


#endif //Z3_INCLUSION_GRAPH_H
