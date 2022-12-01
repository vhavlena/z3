
#ifndef Z3_INCLUSION_GRAPH_H
#define Z3_INCLUSION_GRAPH_H

#include "inclusion_graph_node.h"

namespace smt::noodler {
    class Graph {
    public:
        Graph() = default;

        std::set<GraphNode> nodes;
        std::unordered_map<GraphNode*, std::unordered_set<GraphNode*>> edges;

        void add_edge(GraphNode* source, GraphNode* target) {
            edges[source].insert(target);
        }
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
