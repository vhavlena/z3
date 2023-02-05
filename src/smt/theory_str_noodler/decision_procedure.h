#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

/**
 * @brief Abstract decision procedure. Defines interface for decision 
 * procedures to be used within z3.
 */
class AbstractDecisionProcedure {
public:

    virtual bool compute_next_solution()=0;
    virtual ~AbstractDecisionProcedure()=default;
};

namespace smt::noodler {
    struct SolvingState {
        AutAssignment aut_ass;
        std::deque<std::shared_ptr<GraphNode>> nodes_to_process;
        std::shared_ptr<Graph> inclusion_graph;
        std::unordered_set<BasicTerm> length_sensitive_vars;

        // substitution_map[x] maps variable x to the concatenation of variables for which x was substituted
        // each variable should be either assigned in aut_ass or substituted in this map
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        SolvingState() = default;
        SolvingState(AutAssignment aut_ass,
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
            assert(inclusion_graph->get_nodes().count(processed_node) > 0);
            Graph graph_to_copy = *inclusion_graph;
            graph_to_copy.remove_all_edges();
            assert(graph_to_copy.get_nodes().count(processed_node) > 0);
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

        /**
         * @brief Combines aut_ass and substitution_map into one AutAssigment
         * 
         * For example, if we have aut_ass[x] = aut1, aut_ass[y] = aut2, and substitution_map[z] = xy, then this will return
         * automata assignment ret_ass where ret_ass[x] = aut1, ret_ass[y] = aut2, and ret_ass[z] = concatenation(aut1, aut2)
         * 
         */
        AutAssignment flatten_substition_map() {
            AutAssignment result = aut_ass;
            std::function<std::shared_ptr<Mata::Nfa::Nfa>(const BasicTerm&)> flatten_var;

            flatten_var = [&result, &flatten_var, this](const BasicTerm &var) -> std::shared_ptr<Mata::Nfa::Nfa> {
                if (result.count(var) == 0) {
                    std::shared_ptr<Mata::Nfa::Nfa> var_aut = std::make_shared<Mata::Nfa::Nfa>();
                    auto state = var_aut->add_state();
                    var_aut->initial.add(state);
                    var_aut->final.add(state);
                    for (const auto &subst_var : this->substitution_map.at(var)) {
                        var_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*var_aut, *flatten_var(subst_var)));
                    }
                    result[var] = var_aut;
                    return var_aut;
                } else {
                    return result[var];
                }
            };
            for (const auto &subst_map_pair : substitution_map) {
                flatten_var(subst_map_pair.first);
            }
            return result;
        }
    };

    class DecisionProcedure : public AbstractDecisionProcedure {
    private:
        // prefix of newly created vars during the procedure
        const std::string VAR_PREFIX = "tmp";
        // counter of noodlifications, so that newly created variables will have unique names per noodlification
        // by for example setting the name to VAR_PREFIX + "_" + noodlification_no + "_" + index_in_the_noodle
        unsigned noodlification_no = 0;

        std::deque<SolvingState> worklist;
    public:


        DecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass, const std::unordered_set<BasicTerm> init_length_sensitive_vars);

        // returns true if there is something in worklist that is satisfiable and saves the satisfying element in solution
        bool compute_next_solution() override;
        SolvingState solution;
    };
}

#endif