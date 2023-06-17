#ifndef _NOODLER_DECISION_PROCEDURE_H_
#define _NOODLER_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"
#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "state_len.h"
#include "formula_preprocess.h"

namespace smt::noodler {

    /**
     * @brief Preprocess options
     */
    enum PreprocessType {
        PLAIN,
        UNDERAPPROX
    };

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

        /**
         * @brief Do some preprocessing (can be called only before init_computation)
         * 
         * @param opt The type of preprocessing
         * @param len_eq_vars Equivalence class holding variables with the same length
         */
        virtual void preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) {
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
        virtual expr_ref get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) {
            throw std::runtime_error("Unimplemented");
        }

        virtual ~AbstractDecisionProcedure()=default;
    };

    /// A state of decision procedure that can lead to a solution
    struct SolvingState {
        // aut_ass[x] assigns variable x to some automaton while substitution_map[x] maps variable x to
        // the concatenation of variables for which x was substituted (i.e. its automaton is concatenation
        // of the automata from these variables). Each variable is either assigned in aut_ass or
        // substituted in substitution_map, but not both!
        AutAssignment aut_ass;
        std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

        // set of inclusions where we are trying to find aut_ass + substitution_map such that they hold 
        std::set<Predicate> inclusions;
        // set of inclusion from the previous set that for sure are not on cycle in the inclusion graph
        // that would be generated from inclusions
        std::set<Predicate> inclusions_not_on_cycle;

        // contains inclusions where we need to check if it holds (and if not, do something so that the inclusion holds)
        std::deque<Predicate> inclusions_to_process;

        // the variables that have length constraint on them in the rest of formula
        std::unordered_set<BasicTerm> length_sensitive_vars;


        SolvingState() = default;
        SolvingState(AutAssignment aut_ass,
                     std::deque<Predicate> inclusions_to_process,
                     std::set<Predicate> inclusions,
                     std::set<Predicate> inclusions_not_on_cycle,
                     std::unordered_set<BasicTerm> length_sensitive_vars,
                     std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map)
                        : aut_ass(aut_ass),
                          substitution_map(substitution_map),
                          inclusions(inclusions),
                          inclusions_not_on_cycle(inclusions_not_on_cycle),
                          inclusions_to_process(inclusions_to_process),
                          length_sensitive_vars(length_sensitive_vars) {}

        /// pushes inclusion to the beginning of inclusions_to_process but only if it is not in it yet
        void push_front_unique(const Predicate &inclusion) {
            if (std::find(inclusions_to_process.begin(), inclusions_to_process.end(), inclusion) == inclusions_to_process.end()) {
                inclusions_to_process.push_front(inclusion);
            }
        }

        /// pushes node to the end of nodes_to_process but only if it is not in it yet
        void push_back_unique(const Predicate &inclusion) {
            if (std::find(inclusions_to_process.begin(), inclusions_to_process.end(), inclusion) == inclusions_to_process.end()) {
                inclusions_to_process.push_back(inclusion);
            }
        }

        /// pushes node either to the end or beginning of inclusions_to_process (according to @p to_back) but only if it is not in it yet
        void push_unique(const Predicate &inclusion, bool to_back) {
            if (to_back) {
                push_back_unique(inclusion);
            } else {
                push_front_unique(inclusion);
            }
        }

        /**
         * Checks whether @p inclusion would be on cycle in the inclusion graph (can overapproxamte
         * and say that inclusion is on cycle even if it is not).
         */
        bool is_inclusion_on_cycle(const Predicate &inclusion) {
            return (inclusions_not_on_cycle.count(inclusion) == 0);
        }

        /**
         * Adds inclusion @p inclusion to this solving state (i.e. we will start checking if
         * this inclusion should not be added to inclusion_to_process during the decision procedure). 
         * 
         * @param inclusion Inclusion to add
         * @param is_on_cycle Whether the inclusion would be on cycle in the inclusion graph (if not sure, set to true)
         */
        void add_inclusion(const Predicate &inclusion, bool is_on_cycle = true) {
            inclusions.insert(inclusion);
            if (!is_on_cycle) {
                inclusions_not_on_cycle.insert(inclusion);
            }
        }

        /**
         * Adds inclusion with sides @p left_side and @p right_side to this solving state (i.e. we will start checking if
         * this inclusion should not be added to inclusion_to_process during the decision procedure).
         * 
         * @param left_side Left side of the new inclusion
         * @param right_side Right side of the new inclusion
         * @param is_on_cycle Whether the inclusion would be on cycle in the inclusion graph (if not sure, set to true)
         * @return The newly added inclusion
         */
        Predicate add_inclusion(const std::vector<BasicTerm> &left_side, const std::vector<BasicTerm> &right_side, bool is_on_cycle = true) {
            Predicate new_inclusion{PredicateType::Equation, std::vector<std::vector<BasicTerm>> {left_side, right_side}};
            add_inclusion(new_inclusion);
            return new_inclusion;
        }

        void remove_inclusion(const Predicate &inclusion) {
            inclusions.erase(inclusion);
            inclusions_not_on_cycle.erase(inclusion);
        }

        /**
         * Returns the vector of inclusions that would depend on the given @p inclusion in the inclusion graph.
         * That this all inclusions whose right side contain some variable from the left side of the given @p inclusion.
         * 
         * @param inclusion Inclusion whose dependencies we are looking for
         * @return The set of inclusions that depend on @p inclusion
         */
        std::vector<Predicate> get_dependent_inclusions(const Predicate &inclusion) {
            std::vector<Predicate> dependent_inclusions;
            auto left_vars_set = inclusion.get_left_set();
            for (const Predicate &other_inclusion : inclusions) {
                if (is_dependent(left_vars_set, other_inclusion.get_right_set())) {
                    dependent_inclusions.push_back(other_inclusion);
                }
            }
            return dependent_inclusions;
        }

        /**
         * Check if the vector @p right_side_vars depends on @p left_side_vars, i.e. if some variable
         * (NOT literal) occuring in @p right_side_vars occurs also in @p left_side_vars
         */
        static bool is_dependent(const std::set<BasicTerm> &left_side_vars, const std::set<BasicTerm> &right_side_vars) {
            if (left_side_vars.empty()) {
                return false;
            }
            for (auto const &right_var : right_side_vars) {
                if (right_var.is_variable() && left_side_vars.count(right_var) > 0) {
                    return true;
                }
            }
            return false;
        }

        // substitutes vars and merge same nodes + delete copies of the merged nodes from the inclusions_to_process (and also nodes that have same sides are deleted)
        void substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map);

        /**
         * @brief Combines aut_ass and substitution_map into one AutAssigment
         *
         * For example, if we have aut_ass[x] = aut1, aut_ass[y] = aut2, and substitution_map[z] = xy, then this will return
         * automata assignment ret_ass where ret_ass[x] = aut1, ret_ass[y] = aut2, and ret_ass[z] = concatenation(aut1, aut2)
         */
        AutAssignment flatten_substition_map();
    };

    class DecisionProcedure : public AbstractDecisionProcedure {
    protected:
        // counter of noodlifications
        unsigned noodlification_no = 0;

        // a deque containing states of decision procedure, each of them can lead to a solution
        std::deque<SolvingState> worklist;

        /// State of a found satisfiable solution set when one is computed using
        ///  'DecisionProcedure::compute_next_solution()'.
        SolvingState solution;

        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;

        // initial length, formula and automata assignment which can be updated by preprocessing as is used for initializing the decision procedure
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;

        const theory_str_noodler_params& m_params;


        // contains pairs ((a1, a2), (len1, len2)) where we want formula (len2 or (len1 and (a1 != a2))) to hold, see replace_disequalities
        std::map<std::pair<BasicTerm, BasicTerm>,std::pair<LenNode, LenNode>> dis_len;



        expr_ref mk_len_aut_constr(const expr_ref& var, int v1, int v2);
        

        /**
         * Get length formula from the solving state @p state wrt variables @p vars. For each var x in @p vars it
         * creates either equation |x| = |x_1| + ... + |x_n| if x is substituted by 'x_1 ... x_n' or it add
         * constraint created from the automaton to which x is mapped.
         * 
         * @param variable_map Mapping of BasicTerm variables to Z3 expressions
         * @param state Solving state from which the lengths are created
         * @param vars Set of variables for which we create the lenghts (should be some subset of variables)
         * @return expr_ref Length formula
         */
        expr_ref get_length_from_solving_state(const std::map<BasicTerm, expr_ref>& variable_map, const SolvingState &state, const std::unordered_set<smt::noodler::BasicTerm> &vars);


        /**
         * Check that the disequality a1 != a2 is satisfiable. Assumed to be called if the
         * decision procedure returns SAT. Creates length constraint representing the conjunct:
         * "a1 equals one of its chars" and "a2 equals one of its chars" and "a1 != a2"
         * 
         * See also len_diseqs and FormulaPreprocessor::replace_disequalities().
         * 
         * @param state the solving state whose automata assignment and substitution map will be used
         * @param pr pair (a1, a2) of the variables whose disequality we are checking
         */
        expr_ref check_diseq(const SolvingState &state, const std::pair<BasicTerm, BasicTerm>& pr);

        /**
         * Gets the lengths constraints for each disequation. For each diseqation it adds length constraint
         * (|L| != |R| or (|x_1| == |x_2| and check_diseq(a_1,a_2)))
         * where L = x_1 a_1 y_1 and R = x_2 a_2 y_2 were created during FormulaPreprocessor::replace_disequalities()
         * 
         * @param variable_map Mapping of BasicTerm variables to Z3 expressions
         * @param state Solving state from which the lengths are created
         * @return the conjunction of length constraints of each diseqation
         */
        expr_ref len_diseqs(const std::map<BasicTerm, expr_ref>& variable_map, const SolvingState &state);

        /**
         * @brief Replace disequality L != R with equalities and a length constraint saved in dis_len.
         * 
         * @param diseq Disequality to replace
         * @return Formula with equalities
         */
        Formula DecisionProcedure::replace_disequality(Predicate diseq);

    public:
        
        /**
         * Initialize a new decision procedure that can solve word equations
         * (equalities of concatenations of string variables) with regular constraints
         * (variables belong to some regular language represented by automaton) while
         * keeping the length dependencies between variables (for the variables that
         * occur in some length constraint in the rest of the formula).
         * 
         * @param equalities encodes the word equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p equalities to some NFA), assumes all NFAs are non-empty
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param m Z3 AST manager
         * @param m_util_s Z3 string manager
         * @param m_util_a Z3 arithmetic manager
         * @param len_eq_vars Equivalence class holding variables with the same length
         * @param par Parameters for Noodler string theory.
         */
        DecisionProcedure(
             Formula equalities, AutAssignment init_aut_ass,
             std::unordered_set<BasicTerm> init_length_sensitive_vars,
             ast_manager &m, seq_util &m_util_s, arith_util &m_util_a,
             const theory_str_noodler_params &par
        ) : m{m},
            m_util_s{m_util_s},
            m_util_a{m_util_a},
            init_length_sensitive_vars(init_length_sensitive_vars),
            formula(equalities),
            init_aut_ass(init_aut_ass),
            m_params(par) { }
        
        bool compute_next_solution() override;

        /**
         * @brief Get length constraints of the solution (or overapproximation from initial
         * assignment if decision procedure was not run yet)
         *
         * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
         * @return expr_ref Length formula describing all solutions
         */
        expr_ref get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) override;
        void init_computation() override;

        void preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        expr_ref mk_len_aut(const expr_ref& var, std::set<std::pair<int, int>>& aut_constr);

        std::unordered_set<BasicTerm> &get_init_length_vars() { return init_length_sensitive_vars; }

    };
}

#endif
