#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "nielsen_decision_procedure.h"

namespace smt::noodler {


    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions (currently true)
     */
    expr_ref NielsenDecisionProcedure::get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) {
        expr_ref res(m.mk_true(), m);
        return res;
    }

    /**
     * @brief Initialize computation.
     */
    void NielsenDecisionProcedure::init_computation() {
    }

    /**
     * @brief Preprocessing.
     */
    void NielsenDecisionProcedure::preprocess(PreprocessType opt) {
        // do notning for now
    }

    /**
     * @brief Compute next solution
     * 
     * @return True -> satisfiable
     */
    bool NielsenDecisionProcedure::compute_next_solution() {
        return false;
    }

    NielsenDecisionProcedure::NielsenDecisionProcedure(
             const Formula &equalities, AutAssignment init_aut_ass,
             const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
             ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
             const theory_str_noodler_params& par
     ) :  m{ m }, m_util_s{ m_util_s }, m_util_a{ m_util_a }, init_length_sensitive_vars{ init_length_sensitive_vars },
         formula { equalities },
         init_aut_ass{ init_aut_ass },
         m_params(par) {
         }

    /**
     * @brief Get all possible applicable rewriting rules from a predicate
     * 
     * @param pred Equation
     * @return std::set<NielsenGraph::Label> All possible Nielsen rewriting rules
     */
    std::set<NielsenGraph::Label> NielsenDecisionProcedure::get_rules_from_pred(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();
        std::set<NielsenGraph::Label> ret;

        if(left.size() > 0 && left[0].is_variable() && right.size() > 0) {
            ret.insert({left[0], Concat({right[0], left[0]})});
        }
        if(right.size() > 0 && right[0].is_variable() && left.size() > 0) {
            ret.insert({right[0], Concat({left[0], right[0]})});
        }
        if(left.size() > 0 && left[0].is_variable()) {
            ret.insert({left[0], Concat()});
        }
        if(right.size() > 0 && right[0].is_variable()) {
            ret.insert({right[0], Concat()});
        }

        return ret;
    }

    /**
     * @brief Generate Nielsen graph from a formula.
     * 
     * @param init Initial node (formula)
     * @return NielsenGraph 
     */
    NielsenGraph NielsenDecisionProcedure::generate_from_formula(const Formula& init) const {
        NielsenGraph graph;
        std::set<Formula> generated;
        std::deque<std::pair<size_t, Formula>> worklist;
        worklist.push_back({0, trim_formula(init)}); 

        while(!worklist.empty()) {
            std::pair<size_t, Formula> pr = worklist.front();
            size_t index = pr.first;
            generated.insert(pr.second);
            worklist.pop_front();

            std::vector<Predicate> predicates = pr.second.get_predicates();
            if(is_pred_unsat(predicates[index])) {
                return graph;
            }
            for(; index < predicates.size(); index++) {
                if(!is_pred_sat(predicates[index])) {
                    break;
                }
            }

            std::set<NielsenGraph::Label> rules = get_rules_from_pred(predicates[index]);
            for(const auto& label : rules) {
                Formula rpl = trim_formula(pr.second.replace(Concat({label.first}), label.second));
                graph.add_edge(pr.second, rpl, label);
                if(generated.find(rpl) == generated.end()) {
                    worklist.push_back({index, rpl});
                }
            }
        }

        return graph;
    }

    /**
     * @brief Trim formula. Trim each predicate in the formula. A predicate is trimmed 
     * if it does not contain the same BasicTerm at the beginning of sides.
     * 
     * @param formula Formula
     * @return Formula Trimmed formula
     */
    Formula NielsenDecisionProcedure::trim_formula(const Formula& formula) const {
        Formula ret;

        for(const Predicate& pred : formula.get_predicates()) {
            auto params = pred.get_params();
            size_t len = std::min(params[0].size(), params[1].size());
            size_t i = 0;
            for(; i < len; i++) {
                if(params[0][i] != params[1][i]) {
                    break;
                }
            }
            std::vector<Concat> sides({
                Concat(params[0].begin()+i, params[0].end()),
                Concat(params[1].begin()+i, params[1].end())
            });
            ret.add_predicate(Predicate(PredicateType::Equation, sides));
        }
        return ret;
    }

    /**
     * @brief Check if a predicate is trivially unsat.
     * 
     * @param pred Predicate
     * @return true -> unsat
     */
    bool NielsenDecisionProcedure::is_pred_unsat(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();

        if(left.size() == 0 && right.size() > 0 && right[0].is_literal()) {
            return true;
        }
        if(right.size() == 0 && left.size() > 0 && left[0].is_literal()) {
            return true;
        }
        if(left.size() > 0 && right.size() > 0 && right[0].is_literal() && left[0].is_literal() && right[0] != left[0]) {
            return true;
        }
        return false;
    }

} // Namespace smt::noodler.
