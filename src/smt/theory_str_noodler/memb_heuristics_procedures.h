#ifndef _NOODLER_MEMB_HEURISTICS_PROCEDURES_H_
#define _NOODLER_MEMB_HEURISTICS_PROCEDURES_H_

#include "decision_procedure.h"
#include "regex.h"

namespace smt::noodler {

    /**
     * @brief Decision procedure for one regex membership contraint
     * 
     * It uses some heuristics to check if the regex is universal/empty
     * which can then be easily used to decide if the contraint holds.
     * If the heuristics are not enough, for the case we have `x not in RE`
     * we create the automaton for RE and check if it is equal to universal
     * automaton, which should be better than complementation, as it can blow up
     */
    class MembHeuristicProcedure : public AbstractDecisionProcedure {
        BasicTerm var;
        expr_ref regex;
        bool is_regex_positive;
        const seq_util& m_util_s;
    public:
        MembHeuristicProcedure(BasicTerm var, expr_ref regex, bool is_regex_positive, const seq_util& m_util_s)
            : var(var), regex(regex), is_regex_positive(is_regex_positive), m_util_s(m_util_s) {}

        lbool compute_next_solution() override;
    };
}

#endif
