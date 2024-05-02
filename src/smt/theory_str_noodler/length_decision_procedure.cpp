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

    std::pair<LenNode, LenNodePrecision> LengthDecisionProcedure::get_lengths() {
        /**
         * TODO
         */
        throw std::runtime_error("unimplemented");
    }

    void LengthDecisionProcedure::init_computation() {
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {

        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        STRACE("str", tout << "len: Preprocessing\n");

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities(); // only makes variable a literal or removes the disequation 

        // Underapproximate if it contains inequations
        for (const BasicTerm& t : this->formula.get_vars()) {
            if (prep_handler.get_aut_assignment().is_co_finite(t)) {
                prep_handler.underapprox_languages();
                this->precision = LenNodePrecision::UNDERAPPROX;
                STRACE("str", tout << " - UNDERAPPROXIMATE languages\n";);
                break;
            }
        }

        prep_handler.propagate_eps();
        prep_handler.propagate_variables();
        prep_handler.generate_identities();
        prep_handler.propagate_variables();
        prep_handler.remove_trivial();
        
        // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        }

        return l_undef;
    }

    bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
        STRACE("str", tout << "len: suitability: ";);
        for (const Predicate& pred : form.get_predicates()) {
            if(!pred.is_eq_or_ineq()) {
                STRACE("str", tout << "False - non-equation predicate\n");
                return false;
            }
        }

        for (const BasicTerm& t : form.get_vars()) {
            // t has language of sigma*
            if(init_aut_ass.at(t)->num_of_states() <= 1) {
                    continue;
            }

            // t is co-finite (we can underapproximate it)
            if(init_aut_ass.is_co_finite(t)) {
                continue;
            }

            // t is a literal - get shortest words
            if(init_aut_ass.is_singleton(t)) {
                continue;
            }
            STRACE("str", tout << "False - regular constraints on variable " << t << std::endl;);
            return false;
        }

        STRACE("str", tout << "True\n"; );
        return true;
    }

}