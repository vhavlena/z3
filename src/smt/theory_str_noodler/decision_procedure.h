#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "state_len.h"
#include "formula_preprocess.h"

namespace smt::noodler {
    /**
     * @brief Abstract decision procedure. Defines interface for decision
     * procedures to be used within z3.
     */
    class AbstractDecisionProcedure {
    public:

        /**
         * @brief Initialize the computation (supposed to be called after preprocess)
         */
        virtual void init_computation() {
            throw std::runtime_error("Unimplemented");
        }

        virtual void preprocess() {
            throw std::runtime_error("preprocess unimplemented");
        }

        /**
         * Compute next solution and save the satisfiable solution.
         * @return True if there is an satisfiable element in the worklist.
         */
        virtual bool compute_next_solution() {
            throw std::runtime_error("Not implemented");
        }

        /**
         * Get lengths for problem instance.
         * @param variable_map: map of the BasicTerm variables to Z3 variables
         * @return Conjunction of lengths of the current solution for variables in constructor
         *  (variable renames, init length variables).
         */
        virtual expr_ref get_lengths(std::map<BasicTerm, expr_ref>& variable_map) {
            throw std::runtime_error("Unimplemented");
        }

        virtual ~AbstractDecisionProcedure()=default;
    };

    /**
     * @brief Debug instance of the Decision procedure. Always says SAT and return some length
     * constraints. Simulates the situation when each instance has exactly 10 noodles.
     */
    class DecisionProcedureDebug : public AbstractDecisionProcedure {
    private:
        StateLen<int> state;
        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;
        Instance inst{};
        LengthConstr* solution{ nullptr };

    public:
        DecisionProcedureDebug(const Instance& inst, LengthConstr& len,
                               ast_manager& mn, seq_util& util_s, arith_util& util_a
        ) : state{}, m{ mn }, m_util_s{ util_s }, m_util_a{ util_a } {
            this->inst = inst;
            this->solution = &len;
            this->state.add(inst, 0);
        }

        bool compute_next_solution() override {
            int cnt = this->state.get_val(inst);
            if(cnt >= 10) {
                return false;
            }

            expr_ref refinement_len(m);
            app* atom;
            for (const auto& eq : inst) {
                obj_hashtable<expr> vars;
                util::get_str_variables(to_app(eq), this->m_util_s, this->m, vars);

                for(expr * const var : vars) {
                    expr_ref len_str_l(m_util_s.str.mk_length(var), m);
                    SASSERT(len_str_l);
                    expr_ref num(m);
                    num = this->m_util_a.mk_numeral(rational(cnt), true);
                    atom = this->m_util_a.mk_le(len_str_l, num);
                    refinement_len = refinement_len == nullptr ? atom : m.mk_and(refinement_len, atom);
                }
            }

            this->state.update_val(inst, cnt+1);
            *solution = refinement_len;
            return true;
        }

        ~DecisionProcedureDebug() { }

    };


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
        std::shared_ptr<GraphNode> make_deep_copy_of_inclusion_graph_only_nodes(std::shared_ptr<GraphNode> processed_node);

        // substitutes vars and merge same nodes + delete copies of the merged nodes from the nodes_to_process (and also nodes that have same sides are deleted)
        void substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map);

        /**
         * @brief Combines aut_ass and substitution_map into one AutAssigment
         *
         * For example, if we have aut_ass[x] = aut1, aut_ass[y] = aut2, and substitution_map[z] = xy, then this will return
         * automata assignment ret_ass where ret_ass[x] = aut1, ret_ass[y] = aut2, and ret_ass[z] = concatenation(aut1, aut2)
         *
         */
        AutAssignment flatten_substition_map();
    };

    class DecisionProcedure : public AbstractDecisionProcedure {
    protected:
        // prefix of newly created vars during the procedure
        // TODO there is a small possibility that such a variable already exists, we should either check how to call tmp variables or better, add to normal variables some prefix?
        const std::string VAR_PREFIX = "tmp";
        // counter of noodlifications, so that newly created variables will have unique names per noodlification
        // by for example setting the name to VAR_PREFIX + "_" + noodlification_no + "_" + index_in_the_noodle
        unsigned noodlification_no = 0;

        FormulaPreprocess prep_handler;


        std::deque<SolvingState> worklist;

        /// State of a found satisfiable solution set when one is computed using
        ///  'DecisionProcedure::compute_next_solution()'.
        SolvingState solution;

        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;

        /**
         * @brief Convert all string literals in @c formula to fresh string literals with automata in automata assignment.
         *
         * All string literals are converted to fresh string literals with assigned automata equal to the string literal
         *  expression.
         * We get a new fresh literal for each separate string literal, but multiple occurrences of the same string
         *  literal have the same name.
         */
        void conv_str_lits_to_fresh_lits();

        /**
         * Convert string literals on a single side to fresh string literals with the same literals having the same name.
         * @param side Side for which to convert literals in place.
         * @param fresh_lits_counter Counter for unique trailing numbers where to start for creating unique names of
         *  fresh string literals.
         * @param converted_str_literals Map of found string literals to their fresh names.
         */
        void conv_str_lits_to_fresh_lits_for_side(std::vector<BasicTerm>& side, size_t& fresh_lits_counter,
                                                  std::map<zstring, std::string>& converted_str_literals);


        expr_ref mk_len_aut_constr(const expr_ref& var, int v1, int v2);
        expr_ref mk_len_aut(const expr_ref& var, std::set<std::pair<int, int>>& aut_constr);

        bool check_diseqs(const AutAssignment& ass);

    public:
        DecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass,
                          const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                          ast_manager& m, seq_util& m_util_s, arith_util& m_util_a
        );

        bool compute_next_solution() override;
        expr_ref get_lengths(std::map<BasicTerm, expr_ref>& variable_map) override;
        void init_computation() override;

        void preprocess() override;
    };
}

#endif
