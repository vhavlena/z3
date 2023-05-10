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
