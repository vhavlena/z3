#ifndef _NOODLER_LANG_DECISION_PROCEDURE_H_
#define _NOODLER_LANG_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"
#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "state_len.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    class LangDecisionProcedure : public AbstractDecisionProcedure {
    protected:

        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        bool solved = false;

        bool sat_lang_constr(const Predicate&pred);

    public:
        LangDecisionProcedure(ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, const theory_str_noodler_params& par);

        LangDecisionProcedure(ast_manager& m, seq_util& m_util_s, arith_util& m_util_a);
        
        /**
         * Initialize a new decision procedure that can solve word equations
         * (equalities of concatenations of string variables) with regular constraints
         * (variables belong to some regular language represented by automaton) while
         * keeping the length dependencies between variables (for the variables that
         * occur in some length constraint in the rest of the formula).
         * 
         * @param equalities encodes the word equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p equalities to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param m Z3 AST manager
         * @param m_util_s Z3 string manager
         * @param m_util_a Z3 arithmetic manager
         * @param par Parameters for Noodler string theory.
         */
        LangDecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
                           const theory_str_noodler_params& par
         );

        bool compute_next_solution() override;
        expr_ref get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) override;
        void init_computation() override;

        void preprocess(PreprocessType opt = PreprocessType::PLAIN) override;

        expr_ref mk_len_aut(const expr_ref& var, std::set<std::pair<int, int>>& aut_constr);

    };
}

#endif
