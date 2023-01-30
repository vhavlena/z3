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
#include "formula.h"

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
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variables(arg, m_util_s, m, res);
        }
    }

    /**
     * Get symbols from a given expression @p ex. Append to the output parameter @p alphabet.
     * @param ex Expression to be checked for symbols.
     * @param m_util_s Seq util for AST.
     * @param m AST manager.
     * @param[out] alphabet A set of symbols with where found symbols are appended to.
     */
    void get_symbols(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet);

    using expr_pair = std::pair<expr_ref, expr_ref>;
    using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

    /**
     * Get dummy symbols (one for each disequation in @p disequations).
     *
     * @param disequations Vector of disequations.
     * @param symbols_to_append_to Set of symbols where dummy symbols are appended to.
     * @return Set of dummy symbols.
     */
    std::set<uint32_t> get_dummy_symbols(vector<expr_pair>& disequations, std::set<uint32_t>& symbols_to_append_to);

    /**
     * Get symbolf for formula.
     * @param equations Vector of equations in formula to get symbols from.
     * @param disequations Vector of disequations in formula to get symbols from.
     * @param regexes Vector of regexes in formula to get symbols from.
     * @param m_util_s Seq util for AST.
     * @param m AST manager.
     * @return Set of symbols in the whole formula.
     */
    std::set<uint32_t> get_symbols_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const seq_util& m_util_s,
            const ast_manager& m
    );

    /**
     * Convert expression @p expr to regex in hexadecimal format accepted by RE2.
     * @param[in] expr Expression to be converted to regex.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[in] alphabet Alphabet to be used in re.allchar (SMT2: '.') expressions.
     * @return The resulting regex.
     */
    std::string conv_to_regex_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m,  const std::set<uint32_t>& alphabet);

    /**
    Collect basic terms (vars, literals) from a concatenation @p ex. Append the basic terms 
    to the output parameter @p terms. 
    @param ex Expression to be checked for basic terms.
    @param m_util_s Seq util for AST
    @param pred_replace Replacement of predicate and functions
    @param[out] terms Vector of found BasicTerm (in right order).
    */
    static inline void collect_terms(app* const ex, const seq_util& m_util_s, 
        obj_map<expr, expr*>& pred_replace, std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) {
            std::string lit = ex->get_parameter(0).get_zstring().encode();
            terms.emplace_back(BasicTermType::Literal, lit);
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
            std::string var = ex->get_decl()->get_name().str();
            terms.emplace_back(BasicTermType::Variable, var);
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m_util_s, pred_replace, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m_util_s, pred_replace, terms);
        collect_terms(a_y, m_util_s, pred_replace, terms);
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

    /**
     * @brief Create a fresh int variable.
     * 
     * @param name Infix of the name (rest is added to get a unique name)
     * @param m ast manager
     * @param m_util_s string ast util
     * @param m_util_a arith ast util
     * @return expr_ref Fresh variable
     */
    static expr_ref mk_int_var_fresh(const std::string& name, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a) { /// WARNING: Already present in theory_str_noodler.h, we need to consolidate
        sort * int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);
        expr_ref var(m_util_s.mk_skolem(m.mk_fresh_var_name(name.c_str()), 0,
            nullptr, int_sort), m);
        return var;
    }
        
    /**
     * @brief Create a fresh int variable.
     * 
     * @param name Infix of the name (rest is added to get a unique name)
     * @param m ast manager
     * @param m_util_s string ast util
     * @return expr_ref Fresh variable
     */
    static expr_ref mk_str_var(const std::string& name, ast_manager& m, seq_util& m_util_s) {
        expr_ref var(m_util_s.mk_skolem(symbol(name), 0,
            nullptr, m_util_s.mk_string_sort()), m);
        return var;
    }

    /**
     * @brief Convert Length node to z3 length formula
     * 
     * @param node Length node
     * @param variable_map mapping of variables(BasicTerms) to the corresponding z3 variables(expr_ref)
     * @param m ast manager
     * @param m_util_s string ast util
     * @param m_util_a arith ast util
     * @return expr_ref 
     */
    static expr_ref len_to_expr(const LenNode * node, std::map<BasicTerm, expr_ref>& variable_map, ast_manager &m, seq_util& m_util_s, arith_util& m_util_a) {
        assert(node->succ.size() <= 2);

        switch(node->type) {
        case LenFormulaType::LEAF:
            if(node->atom_val.is_literal())
                return expr_ref(m_util_a.mk_int(std::stoi(node->atom_val.get_name())), m);
            else { 
                auto it = variable_map.find(node->atom_val);
                expr_ref var_expr(m);
                if(it != variable_map.end()) { // if the variable is not found, it was introduced in the preprocessing -> create a new z3 variable
                    var_expr = it->second;
                } else {
                    var_expr = mk_str_var(node->atom_val.get_name(), m, m_util_s);
                }
                return var_expr;
            }
        
        case LenFormulaType::PLUS: {
            assert(node->succ.size() >= 2);
            expr_ref plus = len_to_expr(node->succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node->succ.size(); i++) {
                plus = m_util_a.mk_add(plus, len_to_expr(node->succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return plus;
        }

        case LenFormulaType::EQ: {
            assert(node->succ.size() == 2);
            expr_ref left = len_to_expr(node->succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node->succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m.mk_eq(left, right), m);
        }

        case LenFormulaType::LEQ: {
            assert(node->succ.size() == 2);
            expr_ref left = len_to_expr(node->succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node->succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_le(left, right), m);
        }

        case LenFormulaType::AND: {
            if(node->succ.size() == 0)
                return expr_ref(m.mk_true(), m);
            expr_ref andref = len_to_expr(node->succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node->succ.size(); i++) {
                andref = m.mk_and(andref, len_to_expr(node->succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return andref;
        }

        default:
            assert(false);
        }
    }
    
}

#endif
