#ifndef _NOODLER_LENGTH_DECISION_PROCEDURE_H_
#define _NOODLER_LENGTH_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    /**
     * @brief Length-based decision procedure.
     * 
     */
    class LengthDecisionProcedure : public AbstractDecisionProcedure {
    private:
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

    public:
        
        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p form to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         */
        LengthDecisionProcedure(const Formula &form, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           const theory_str_noodler_params& par
         ) : init_length_sensitive_vars{ init_length_sensitive_vars },
             formula { form },
             init_aut_ass{ init_aut_ass },
             m_params(par) { 
            
            /**
             * TODO
             */
        }

        lbool compute_next_solution() override;
        LenNode get_initial_lengths() override {
            return LenNode(LenFormulaType::TRUE);
        }
        LenNode get_lengths() override;
        void init_computation() override;

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        static bool is_suitable(const Formula &form, const AutAssignment& init_aut_ass);

    };
}

#endif
