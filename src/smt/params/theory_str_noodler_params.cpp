
#include "smt/params/theory_str_noodler_params.h"
#include "smt/params/smt_params_helper.hpp"

void theory_str_noodler_params::updt_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_underapproximation = p.str_underapprox();
    m_preprocess_red = p.str_preprocess_red();
    m_loop_protect = p.str_loop_protect();
}

#define DISPLAY_PARAM(X) out << #X"=" << X << std::endl;

void theory_str_noodler_params::display(std::ostream & out) const {
    DISPLAY_PARAM(m_underapproximation);
    DISPLAY_PARAM(m_preprocess_red);
}
