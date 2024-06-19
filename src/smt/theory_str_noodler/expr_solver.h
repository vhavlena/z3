/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include "smt/smt_context.h"

namespace smt::noodler {
    class int_expr_solver {
        bool unsat_core=false;
        ast_manager& m;
        bool initialized;
        expr_ref_vector erv;
    public:
        kernel m_kernel;
    public:
        int_expr_solver(ast_manager& m, smt_params fp):
                m(m),erv(m),m_kernel(m, fp){
            fp.m_string_solver = symbol("none");
            initialized=false;
       }

        lbool check_sat(expr* e, bool produce_model, model_ref &res_model);

            // model_ref mod;
            // m_kernel.get_model(mod);
            // std::cout << *mod << std::endl;

            STRACE("str-lia",
                if(r==lbool::l_false){
                    tout << "UNSAT core:" << std::endl;
                    for(unsigned i=0; i < m_kernel.get_unsat_core_size(); i++) {
                        tout << mk_pp(m_kernel.get_unsat_core_expr(i), m) << std::endl;
                    }
                }
            );

        void assert_expr(expr * e);
    };
}

#endif