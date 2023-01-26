#ifndef _NOODLER_UTIL_H_
#define _NOODLER_UTIL_H_

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

namespace smt::noodler::util {

    /**
    Get variable from a given expression @p ex. Append to the output parameter @p res. 
    @param ex Expression to be checked for variables.
    @param m_util_s Seq util for AST
    @param m AST manager
    @param[out] res Vector of found variables (may contain duplicities).
    */
    static void get_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variables(arg, m_util_s, m, res);
        }
    };

    /**
    Collect basic terms (vars, literals) from a concatenation @p ex. Append the basic terms 
    to the output parameter @p terms. 
    @param ex Expression to be checked for basic terms.
    @param m_util_s Seq util for AST
    @param[out] terms Vector of found BasicTerm (in right order).
    */
    static inline void collect_terms(const app* ex, const seq_util& m_util_s, std::vector<BasicTerm>& terms) {
        if(m_util_s.str.is_string(ex)) {
            std::string lit = ex->get_parameter(0).get_zstring().encode();
            terms.push_back(BasicTerm(BasicTermType::Literal, lit));
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
            std::string var = ex->get_decl()->get_name().str();
            terms.push_back(BasicTerm(BasicTermType::Variable, var));
            return;
        }

        SASSERT(m_util_s.str.is_concat(ex));
        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m_util_s, terms);
        collect_terms(a_y, m_util_s, terms);
    }

    static inline void get_len_exprs(app* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res) {
        if(m_util_s.str.is_length(ex)) {
            res.insert(ex);
            return;
        }

        for(unsigned i = 0; i < ex->get_num_args(); i++) {
            SASSERT(is_app(ex->get_arg(i)));
            app *arg = to_app(ex->get_arg(i));
            get_len_exprs(arg, m_util_s, m, res);
        }
    }
    
}

#endif