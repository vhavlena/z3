#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "lang_decision_procedure.h"

namespace smt::noodler {

    bool LangDecisionProcedure::sat_lang_constr(const Predicate&pred) {
        if(pred.get_left_side().size() != pred.get_right_side().size() || pred.get_right_side().size() != 1) {
            util::throw_error("size mismatch");
        }

        std::cout << pred.to_string() << std::endl;

        BasicTerm t1 = pred.get_left_side()[0];
        BasicTerm t2 = pred.get_right_side()[0];
        if(t1.get_type() != BasicTermType::Lang || t2.get_type() != BasicTermType::Lang) {
            util::throw_error("only comparison of languages is supported");
        }

        Mata::Nfa::Nfa nfa1 = *this->init_aut_ass.at(t1);
        Mata::Nfa::Nfa nfa2 = *this->init_aut_ass.at(t2);
        bool eq = Mata::Nfa::are_equivalent(nfa1, nfa2);

        if(pred.get_type() == PredicateType::Equation) {
            return eq;
        } else if(pred.get_type() == PredicateType::Inequation) {
            return !eq;
        }
        
        util::throw_error("unsupported predicate type");
    }

    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions
     */
    expr_ref LangDecisionProcedure::get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) {
        expr_ref res(m.mk_false(), m);
        return res;
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void LangDecisionProcedure::init_computation() {
        this->solved = false;
    }

    /**
     * @brief Preprocessing.
     */
    void LangDecisionProcedure::preprocess(PreprocessType opt) {
        // do notning for now
    }

    bool LangDecisionProcedure::compute_next_solution() {
        if(this->solved) return false;
        this->solved = true;

        bool res = true;
        for(const Predicate& pr : this->formula.get_predicates()) {
            res = res && sat_lang_constr(pr);
        }

        return res;
    }

    LangDecisionProcedure::LangDecisionProcedure(
             const Formula &equalities, AutAssignment init_aut_ass,
             const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
             ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
             const theory_str_noodler_params& par
     ) :  m{ m }, m_util_s{ m_util_s }, m_util_a{ m_util_a }, init_length_sensitive_vars{ init_length_sensitive_vars },
         formula { equalities },
         init_aut_ass{ init_aut_ass },
         m_params(par) {
         }

} // Namespace smt::noodler.
