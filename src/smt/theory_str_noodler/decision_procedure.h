#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "aut_assignment.h"
#include "state_len.h"

namespace smt::noodler {
    struct WorklistElement {
        AutAssignment aut_ass;
        std::deque<std::shared_ptr<GraphNode>> nodes_to_process;
        std::shared_ptr<Graph> inclusion_graph;
        std::unordered_set<BasicTerm> length_sensitive_vars;

        // substitution_map[x] maps variable x to the concatenation of variables for which x was substituted
        // each variable should be either assigned in aut_ass or substituted in this map
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        WorklistElement() = default;
        WorklistElement(AutAssignment aut_ass,
                        std::deque<std::shared_ptr<GraphNode>> nodes_to_process,
                        std::shared_ptr<Graph> inclusion_graph,
                        std::unordered_set<BasicTerm> length_sensitive_vars,
                        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map)
                        : aut_ass(aut_ass),
                          nodes_to_process(nodes_to_process),
                          inclusion_graph(inclusion_graph), 
                          length_sensitive_vars(length_sensitive_vars),
                          substitution_map(substitution_map) {} 

        // pushes node to the beginning of nodes_to_process but only if it is not in it yet
        void push_front_unique(const std::shared_ptr<GraphNode> &node) {
            if (std::find(nodes_to_process.begin(), nodes_to_process.end(), node) == nodes_to_process.end()) {
                nodes_to_process.push_front(node);
            }
        }

        // pushes node to the end of nodes_to_process but only if it is not in it yet
        void push_back_unique(const std::shared_ptr<GraphNode> &node) {
            if (std::find(nodes_to_process.begin(), nodes_to_process.end(), node) == nodes_to_process.end()) {
                nodes_to_process.push_back(node);
            }
        }

        void push_unique(const std::shared_ptr<GraphNode> &node, bool to_back) {
            if (to_back) {
                push_back_unique(node);
            } else {
                push_front_unique(node);
            }
        }

        // inclusion_graph will become a new deep copy of the existing inclusion_graph
        // edges are removed
        // nodes_to_process are updated so that the pointers point to the nodes of this deep copy
        // processed_node is the node that is being processed, the return value is this node in the deep copy
        // TODO this function is really ugly, I should do something about it
        std::shared_ptr<GraphNode> make_deep_copy_of_inclusion_graph_only_nodes(std::shared_ptr<GraphNode> processed_node) {
            Graph graph_to_copy = *inclusion_graph;
            graph_to_copy.remove_all_edges();
            std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> node_mapping;
            inclusion_graph = std::make_shared<Graph>(graph_to_copy.deep_copy(node_mapping));
            std::deque<std::shared_ptr<GraphNode>> new_nodes_to_process;
            while (!nodes_to_process.empty()) {
                new_nodes_to_process.push_back(node_mapping.at(nodes_to_process.front()));
                nodes_to_process.pop_front();
            }
            nodes_to_process = new_nodes_to_process;
            return node_mapping.at(processed_node);
        }

        // substitutes vars and merge same nodes + delete copies of the merged nodes from the nodes_to_process (and also nodes that have same sides are deleted)
        void substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map) {
            std::unordered_set<std::shared_ptr<GraphNode>> deleted_nodes;
            inclusion_graph->substitute_vars(substitution_map, deleted_nodes);

            // remove all deleted_nodes from the nodes_to_process (using remove/erase)
            // TODO: is this correct?? I assume that if we delete copy of a merged node from nodes_to_process, it either does not need to be processed or the merged node will be in nodes_to_process
            auto is_deleted = [&deleted_nodes](std::shared_ptr<GraphNode> node) { return (deleted_nodes.count(node) > 0) ; };
            nodes_to_process.erase(std::remove_if(nodes_to_process.begin(), nodes_to_process.end(), is_deleted), nodes_to_process.end());
        }
    };

    class DecisionProcedure  {
    private:
        // prefix of newly created vars during the procedure
        const std::string VAR_PREFIX = "tmp";
        // counter of noodlifications, so that newly created variables will have unique names per noodlification
        // by for example setting the name to VAR_PREFIX + "_" + noodlification_no + "_" + index_in_the_noodle
        unsigned noodlification_no = 0;

        std::deque<WorklistElement> worklist;

        std::shared_ptr<Mata::Nfa::Nfa> automaton_with_empty_word;
    public:


        DecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass, const std::unordered_set<BasicTerm> init_length_sensitive_vars);

        bool get_another_solution();
        WorklistElement sat_element;

        // void initialize(const Instance& inst) override;
        // bool get_another_solution(const Instance& inst, LengthConstr& out) override;
    };
}

#endif