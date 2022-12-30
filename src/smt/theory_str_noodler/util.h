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
    static void get_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, vector<expr*>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
            res.push_back(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);
        SASSERT(m_util_s.str.is_concat(ex_app) || m.is_eq(ex_app));

        SASSERT(ex_app->get_num_args() == 2);
        app *a_x = to_app(ex_app->get_arg(0));
        app *a_y = to_app(ex_app->get_arg(1));
        get_variables(a_x, m_util_s, m, res);
        get_variables(a_y, m_util_s, m, res);
    };
    
}

#endif