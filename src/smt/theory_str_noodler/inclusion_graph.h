
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include <optional>
#include <deque>
#include "inclusion_graph_node.h"

namespace smt::noodler {

    using Nodes = std::unordered_set<std::shared_ptr<GraphNode>>;
    using Edges = std::unordered_map<std::shared_ptr<GraphNode>, Nodes>;
    class Graph {
    private:
        Nodes nodes;
        Edges edges;
        Edges inverse_edges;
        // set of nodes that do not have edge coming to them
        // it is guaranteed to be correct ONLY after creating splitting/inclusion graph
        // methods adding/removing edges DO NOT UPDATE this set, i.e. IT MIGHT NOT BE CORRECT
        // TODO: probably not needed
        std::unordered_set<std::shared_ptr<GraphNode>> initial_nodes;
        // set of nodes that are NOT on some cycle
        // it is guaranteed to be correct ONLY after creating inclusion graph???
        std::unordered_set<std::shared_ptr<GraphNode>> nodes_not_on_cycle;

        void remove_edge_from_edges(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            if (edges.count(source) == 0) {
                return;
            }

            Nodes &source_edges = edges.at(source);
            source_edges.erase(target);
            if (source_edges.empty()) {
                edges.erase(source);
            }
        }

        void remove_edge_from_inverse_edges(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            if (inverse_edges.count(target) == 0) {
                return;
            }

            Nodes &target_edges = inverse_edges.at(target);
            target_edges.erase(source);
            if (target_edges.empty()) {
                inverse_edges.erase(target);
            }
        }

    public:

        const Nodes& get_nodes() const { return nodes; }

        void add_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            edges[source].insert(target);
            inverse_edges[target].insert(source);
        }

        void remove_edge(std::shared_ptr<GraphNode> source, std::shared_ptr<GraphNode> target) {
            remove_edge_from_edges(source, target);
            remove_edge_from_inverse_edges(source, target);
        }

        void remove_edges_from(std::shared_ptr<GraphNode> source) {
            for (const auto &target : edges[source]) {
                remove_edge_from_inverse_edges(source, target);
            }
            edges.erase(source);
        }

        void remove_edges_to(std::shared_ptr<GraphNode> target) {
            for (auto& source: get_edges_to(target)) {
                remove_edge_from_edges(source, target);
            }
            inverse_edges.erase(target);
        }

        void remove_edges_with(std::shared_ptr<GraphNode> node) {
            remove_edges_from(node);
            remove_edges_to(node);
        }

        void remove_all_edges() {
            edges.clear();
            inverse_edges.clear();
        }

        size_t get_num_of_edges() const {
            size_t num_of_edges{ 0 };
            for (const auto& edge_set: edges) {
                num_of_edges += edge_set.second.size();
            }
            return num_of_edges;
        }

        const Edges& get_edges() const { return edges; }

        // assumes there are some edges coming from the source
        const Nodes& get_edges_from(std::shared_ptr<GraphNode> source) {
            return edges.at(source);
        }

        // assumes there are some edges going to the target
        const Nodes& get_edges_to(std::shared_ptr<GraphNode> target) const {
            return inverse_edges.at(target);
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


        std::shared_ptr<GraphNode> add_node(const std::vector<BasicTerm> &left_side, const std::vector<BasicTerm> &right_side) {
            return add_node(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>> {left_side, right_side}));
        }

        void remove_node(const std::shared_ptr<GraphNode> node) {
            remove_edges_with(node);
            nodes.erase(node);
        }

        bool is_on_cycle(const std::shared_ptr<GraphNode> &node) {
            assert(nodes.count(node) > 0);
            return (nodes_not_on_cycle.count(node) == 0);
        }

        // adds edges so that inclusions x and y where left side of x shares variable with right side of y have edge from x to y  
        void add_inclusion_graph_edges();

        // makes a deep copy of the garph, i.e. returned graph is semantically same as this graph, but the pointers to nodes are different
        Graph deep_copy() const;
        // node_mapping - maps pointers of this graph into pointers of the returned graph (i.e. the same inclusion is mapped to the same inclusion)
        Graph deep_copy(std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> node_mapping) const;

        // substitutes all vars in left/right sides in nodes based on the substitution_map and merge nodes that become same
        // assumes that there are no edges in the graph
        // in out_deleted_nodes there will be nodes that were deleted, because of merging
        void substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map, std::unordered_set<std::shared_ptr<GraphNode>> &out_deleted_nodes);

        // assumes that formula does not contain same equalities
        static Graph create_inclusion_graph(const Formula& formula, std::deque<std::shared_ptr<GraphNode>> out_node_order);
        static Graph create_simplified_splitting_graph(const Formula& formula);
        static Graph create_inclusion_graph(Graph& simplified_splitting_graph, std::deque<std::shared_ptr<GraphNode>> out_node_order);
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
