
#include "unary_decision_procedure.h"

namespace smt::noodler {
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
