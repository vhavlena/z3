#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "length_decision_procedure.h"

namespace smt::noodler {

lbool LengthDecisionProcedure::compute_next_solution() {
    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

LenNode LengthDecisionProcedure::get_lengths() {
    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

void LengthDecisionProcedure::init_computation() {
    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {
    
    FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
    /**
     * TODO
     */
    throw std::runtime_error("unimplemented");
}

}