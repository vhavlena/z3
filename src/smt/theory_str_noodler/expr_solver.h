/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#ifndef _EXPR_INT_SOLVER_H_
#define _EXPR_INT_SOLVER_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <smt/params/smt_params.h>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"


namespace smt::noodler {
    class int_expr_solver:expr_solver{
        bool unsat_core=false;
        kernel m_kernel;
        ast_manager& m;
        bool initialized;
        expr_ref_vector erv;
    public:
        int_expr_solver(ast_manager& m, smt_params fp):
                m_kernel(m, fp), m(m),erv(m){
            fp.m_string_solver = symbol("none");
            initialized=false;
       }

        lbool check_sat(expr* e) override {
                bool on_screen =false;
    //        m_kernel.push();
            erv.push_back(e);
            lbool r = m_kernel.check(erv);
            erv.pop_back();

            if(on_screen && r==lbool::l_false){
                std::cout<< "UNSAT core:\n";
                for(unsigned i=0;i<m_kernel.get_unsat_core_size();i++){
                    std::cout<<mk_pp(m_kernel.get_unsat_core_expr(i),m)<<std::endl;
                }
            }

    //        m_kernel.pop(1);
            return r;
        }

        void initialize(context& ctx, bool include_ass = true) {
            bool on_screen =false;
            // bool include_ass = true;
            if(!initialized){
                initialized=true;
                expr_ref_vector Assigns(m),Literals(m);
                ctx.get_guessed_literals(Literals);
                ctx.get_assignments(Assigns);
                for (unsigned i = 0; i < ctx.get_num_asserted_formulas(); ++i) {
                    if(on_screen) std::cout<<"check_sat context from asserted:"<<mk_pp(ctx.get_asserted_formula(i),m)<<std::endl;
                    assert_expr(ctx.get_asserted_formula(i));

                }
                for (auto & e : Assigns){
                    if(ctx.is_relevant(e) && include_ass) {
                        if(on_screen) std::cout << "check_sat context from assign:" << mk_pp(e, m) << std::endl;
                        assert_expr(e);
                    }
                    // if(on_screen) std::cout << "is relevant: " << ctx.is_relevant(e) << " get_assignment: "<<ctx.get_assignment(e)<<std::endl;
                }
            //    for (auto & e : Literals){
            //        if(ctx.is_relevant(e)) {
            //            if (on_screen) std::cout << "check_sat context from guess:" << mk_pp(e, m) << std::endl;
            //            assert_expr(e);
            //        }
            //        if(on_screen) std::cout << "is relevant: " << ctx.is_relevant(e) << " get_assignment: "<<ctx.get_assignment(e)<<std::endl;

            //    }

            }
        }

        void assert_expr(expr * e) {
            if(!unsat_core){
                erv.push_back(e);
                // m_kernel.assert_expr(e);

            } else {
                erv.push_back(e);
                lbool r = m_kernel.check(erv);
                if(r==lbool::l_false){
                    std::cout<< "UNSAT core:\n";
                    for(unsigned i=0;i<m_kernel.get_unsat_core_size();i++){
                        std::cout<<mk_pp(m_kernel.get_unsat_core_expr(i),m)<<std::endl;
                    }
                }
            }
        }
    };
}

#endif