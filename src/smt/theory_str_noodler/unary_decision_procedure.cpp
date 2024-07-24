
#include "unary_decision_procedure.h"

namespace smt::noodler {

    LenNode UnaryDecisionProcedure::get_initial_lengths(bool all_vars) {
        if (this->init_length_sensitive_vars.empty()) {
            // there are no length sensitive vars, so we can immediately say true
            return LenNode(LenFormulaType::TRUE);
        }

        // start from length formula from preprocessing
        std::vector<LenNode> conjuncts = {};

        // for each initial length variable get the lengths of all its possible words for automaton in init_aut_ass
        if(all_vars) {
            for (const BasicTerm &var : this->formula.get_vars()) {
                conjuncts.push_back(init_aut_ass.get_lengths(var));
            }
        } else {
            for (const BasicTerm &var : this->init_length_sensitive_vars) {
                conjuncts.push_back(init_aut_ass.get_lengths(var));
            }
        }
        
        return LenNode(LenFormulaType::AND, conjuncts);
    }

    zstring UnaryDecisionProcedure::get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        zstring smb(unsigned(this->symbol));
        zstring ass = "";
        rational length = get_arith_model_of_var(var);
        for(rational i(0); i < length; i++) {
            ass = ass + smb;
        }
        return ass;
    }

}
