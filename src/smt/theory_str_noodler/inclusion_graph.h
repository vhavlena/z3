
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include "inclusion_graph_node.h"

namespace smt::noodler {

    using Nodes = std::unordered_set<std::shared_ptr<GraphNode>>;
    using Edges = std::unordered_map<std::shared_ptr<GraphNode>, Nodes>;
    class Graph {
    protected:
        Nodes nodes;
        Edges edges;
        // set of nodes that do not have edge coming to them
        // it is guaranteed to be correct ONLY after creating splitting/inclusion graph
        // methods adding/removing edges DO NOT UPDATE this set, i.e. IT MIGHT NOT BE CORRECT
        std::unordered_set<std::shared_ptr<GraphNode>> initial_nodes;
        // set of nodes that are NOT on some cycle
        // it is guaranteed to be correct ONLY after creating inclusion graph???
        std::unordered_set<std::shared_ptr<GraphNode>> nodes_not_on_cycle;
    public:

        const Nodes& get_nodes() { return nodes; }

        void add_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            edges[source].insert(target);
        }

        void remove_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            auto source_edges{ edges[source] };
            source_edges.erase(target);
            if (source_edges.empty()) {
                edges.erase(source);
            }
        }

        void remove_edges_from(std::shared_ptr<GraphNode> source) {
            edges.erase(source);
        }

        Nodes get_edges_to(std::shared_ptr<GraphNode> target) const {
            Nodes source_nodes{};
            for (auto& source_edges: edges) {
                if (source_edges.second.find(target) != source_edges.second.end()) {
                    source_nodes.insert(source_edges.first);
                }
            }
            return source_nodes;
        }

        void remove_edges_to(std::shared_ptr<GraphNode> target) {
            for (auto& source: get_edges_to(target)) {
                remove_edge(source, target);
            }
        }

        void remove_edges_with(std::shared_ptr<GraphNode> node) {
            remove_edges_from(node);
            remove_edges_to(node);
        }

        size_t get_num_of_edges() const {
            size_t num_of_edges{ 0 };
            for (const auto& edge_set: edges) {
                num_of_edges += edge_set.second.size();
            }
            return num_of_edges;
        }

        const Edges& get_edges() const { return edges; }

        const Nodes& get_edges_from(std::shared_ptr<GraphNode> source) {
            return edges[source];
        }

        std::shared_ptr<GraphNode> get_node(const Predicate& predicate) {
            auto node = std::find_if(nodes.begin(), nodes.end(), [&predicate](std::shared_ptr<GraphNode> el){ return (el->get_predicate() == predicate);});
            if (node == nodes.end()) { return nullptr; }
            return *node;
        }

        std::shared_ptr<GraphNode> add_node(const Predicate& predicate) {
            // TODO check if added node already does not exists??? by calling get_node?
            std::shared_ptr<GraphNode> new_node = std::make_shared<GraphNode>(predicate);
            nodes.insert(new_node);
            return new_node;
        }

        // assumes that formula does not contain same equalities
        static Graph create_inclusion_graph(const Formula& formula);
        static Graph create_simplified_splitting_graph(const Formula& formula);
        static Graph create_inclusion_graph(Graph& simplified_splitting_graph);
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


}


#endif //Z3_INCLUSION_GRAPH_H
