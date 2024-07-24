#ifndef _NOODLER_UNARY_PROCEDURE_H_
#define _NOODLER_UNARY_PROCEDURE_H_

#include "decision_procedure.h"
#include "regex.h"

namespace smt::noodler {

    /**
     * @brief Decision procedure for system of equations containing a single symbol only (no regular constraints, 
     * conversions, and others).
     * 
     * The satisfiability of unary system of equations (system of equations over singleton alphabet) is 
     * satisfiable iff the lengths are satisfiable. The model is then constructed as a^n where n is a LIA 
     * solution for a particular variable.
     */
    class UnaryDecisionProcedure : public AbstractDecisionProcedure {
        Formula formula;
        AutAssignment init_aut_ass;
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        const theory_str_noodler_params& m_params;
        mata::Symbol symbol;

    public:
        UnaryDecisionProcedure(const Formula& equations, const AutAssignment& init_aut_ass, 
            const std::unordered_set<BasicTerm>& init_length_sensitive_vars, const theory_str_noodler_params& par)
            : formula(equations), init_aut_ass(init_aut_ass), init_length_sensitive_vars(init_length_sensitive_vars), m_params(par) {

            auto alph = this->init_aut_ass.get_alphabet();
            alph.erase(util::get_dummy_symbol());
            VERIFY(alph.size() == 1);
            symbol = *alph.begin();
        }

        lbool compute_next_solution() override { return l_false; };

        /**
         * @brief Get model of the variable @p var. Since there is only a single symbol a in the system, the assignment is 
         * generated as a^n, where n is LIA length model of @p var. 
         * 
         * @param var Variable
         * @param get_arith_model_of_var Length assignment to variables
         * @return zstring String assignment
         */
        zstring get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) override;

        /**
         * @brief Get the initial lengths (similar to DecisionProcedure::get_initial_lengths). 
         * 
         * @param all_vars Generate lengths to all variables?
         * @return LenNode Length constraints
         */
        LenNode get_initial_lengths(bool all_vars = false) override;
    };
}

#endif
