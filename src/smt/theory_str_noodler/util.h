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
#include "aut_assignment.h"

namespace smt::noodler::util {
    using expr_pair = std::pair<expr_ref, expr_ref>;
    using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

    /**
     * Throws error and select which class to throw based on debug (if we are
     * debugging, we do not want z3 to catch our error, if we are not debugging
     * we want z3 to catch it and return unknown).
     * 
     * @param errMsg Error message
     */
    void throw_error(std::string errMsg);

    /**
    Get variables from a given expression @p ex. Append to the output parameter @p res.
    @param ex Expression to be checked for variables.
    @param m_util_s Seq util for AST
    @param m AST manager
    @param[out] res Vector of found variables (may contain duplicities).
    @param pred_map predicate to variable mapping
    */
    void get_str_variables(expr* ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map=nullptr);

    /**
     * Check whether an @p expression is a string variable.
     *
     * Function checks only the top-level expression and is not recursive.
     * Regex variables do not count as string variables.
     * @param expression Expression to check.
     * @return True if @p expression is a variable, false otherwise.
     */
    bool is_str_variable(const expr* expression, const seq_util& m_util_s);

    /**
     * Check whether an @p expression is any kind of variable (string, regex, integer).
     *
     * Function checks only the top-level expression and is not recursive.
     * @param expression Expression to check.
     * @return True if @p expression is a variable, false otherwise.
     */
    bool is_variable(const expr* expression, const seq_util& m_util_s);

    /**
     * Get variable names from a given expression @p ex. Append to the output parameter @p res.
     * @param[in] ex Expression to be checked for variables.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[out] res Vector of found variables (may contain duplicities).
     */
    void get_variable_names(expr* ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res);

    /**
     * Extract symbols from a given expression @p ex. Append to the output parameter @p alphabet.
     * @param[in] ex Expression to be checked for symbols.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[out] alphabet A set of symbols with where found symbols are appended to.
     */
    void extract_symbols(expr * ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet);

    /**
     * Get dummy symbols.
     *
     * @param[in] new_symb_num Number of added symbols.
     * @param[out] symbols_to_append_to Set of symbols where dummy symbols are appended to.
     * @return Set of dummy symbols.
     */
    std::set<uint32_t> get_dummy_symbols(size_t new_symb_num, std::set<uint32_t>& symbols_to_append_to);

    /**
     * Get symbols for formula.
     * @param[in] equations Vector of equations in formula to get symbols from.
     * @param[in] disequations Vector of disequations in formula to get symbols from.
     * @param[in] regexes Vector of regexes in formula to get symbols from.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @return Set of symbols in the whole formula.
     *
     * TODO: Test.
     */
    [[nodiscard]] std::set<uint32_t> get_symbols_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const vector<expr_pair_flag>& lang_regexes,
            const seq_util& m_util_s,
            const ast_manager& m
    );

    /**
     * Get automata assignment for formula.
     * @param[in] equations Vector of equations in formula to get symbols from.
     * @param[in] disequations Vector of disequations in formula to get symbols from.
     * @param[out] var_name Mapping of BasicTerm variables to the corresponding z3 expressions
     * @param[in] regexes Vector of regexes in formula to get symbols from.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @return Automata assignment for the whole formula.
     *
     * TODO: Test.
     */
    [[nodiscard]] AutAssignment create_aut_assignment_for_formula(
            const Formula& instance,
            const vector<expr_pair_flag>& regexes,
            std::map<BasicTerm, expr_ref>& var_name,
            const seq_util& m_util_s,
            const ast_manager& m,
            const std::set<uint32_t>& alphabet
    );

    /**
     * Convert expression @p expr to regex in hexadecimal format accepted by RE2.
     * @param[in] expr Expression to be converted to regex.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[in] alphabet Alphabet to be used in re.allchar (SMT2: '.') expressions.
     * @return The resulting regex.
     */
    [[nodiscard]] std::string conv_to_regex_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m,
                                                const std::set<uint32_t>& alphabet);

    /**
     * Convert expression @p expr to NFA using hexadecimal values as symbols.
     * @param[in] expression Expression to be converted to regex.
     * @param[in] m_util_s Seq util for AST.
     * @param[in] m AST manager.
     * @param[in] alphabet Alphabet to be used in re.allchar (SMT2: '.') expressions.
     * @param[in] make_complement Whether to make complement of the passed @p expr instead.
     * @return The resulting regex.
     */
    [[nodiscard]] Mata::Nfa::Nfa conv_to_nfa(const app *expression, const seq_util& m_util_s, const ast_manager& m,
                                             const std::set<uint32_t>& alphabet, bool make_complement = false);

    /**
     * Create NFA accepting a word in Z3 zstring representation.
     * @param word Word to accept.
     * @return NFA.
     */
    Mata::Nfa::Nfa create_word_nfa(const zstring& word);

    /**
     * Collect basic terms (vars, literals) from a concatenation @p ex. Append the basic terms to the output parameter
     *  @p terms.
     * @param ex Expression to be checked for basic terms.
     * @param m_util_s Seq util for AST
     * @param pred_replace Replacement of predicate and functions
     * @param[out] terms Vector of found BasicTerm (in right order).
     *
     * TODO: Test.
     */
    void collect_terms(app* ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms
    );

    /**
     * Convert variable in @c expr form to @c BasicTerm.
     * @param variable Variable to be converted to @c BasicTerm.
     * @return Passed @p variable as a @c BasicTerm
     *
     * TODO: Test.
     */
    BasicTerm get_variable_basic_term(expr* variable);

    void get_len_exprs(app* ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res);

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

    static expr_ref mk_int_var(const std::string& name, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a) { /// WARNING: Already present in theory_str_noodler.h, we need to consolidate
        sort * int_sort = m.mk_sort(m_util_a.get_family_id(), INT_SORT);
        expr_ref var(m_util_s.mk_skolem(symbol(name), 0,
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
     * @brief Check whether the expression @p val is of the form ( @p num_res ) + (len @p s ).
     * 
     * @param val Expression to be checked
     * @param s String term with length
     * @param m ast manager
     * @param m_util_s string ast util
     * @param m_util_a arith ast util
     * @param[out] num_res expression to be substracked from length term
     * @return Is of the form.
     */
    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res);

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
    static expr_ref len_to_expr(const LenNode &node, const std::map<BasicTerm, expr_ref>& variable_map, ast_manager &m, seq_util& m_util_s, arith_util& m_util_a) {
        switch(node.type) {
        case LenFormulaType::LEAF:
            if(node.atom_val.get_type() == BasicTermType::Length)
                return expr_ref(m_util_a.mk_int(std::stoi(node.atom_val.get_name().encode())), m);
            else if (node.atom_val.get_type() == BasicTermType::Literal) {
                // for literal, get the exact length of it
                // the value of literal can be in literal_value, but also in name (if it is empty)

                // TODO: if I change it to the following, it seems it is working
                return expr_ref(m_util_a.mk_int(node.atom_val.literal_value.length()), m);

                // if (node.atom_val.literal_value.length() > 0) {
                //     return expr_ref(m_util_a.mk_int(node.atom_val.literal_value.length()), m);
                // } else {
                //     return expr_ref(m_util_a.mk_int(node.atom_val.get_name().length()), m);
                // }
            } else {
                auto it = variable_map.find(node.atom_val);
                expr_ref var_expr(m);
                if(it != variable_map.end()) { // if the variable is not found, it was introduced in the preprocessing -> create a new z3 variable
                    var_expr = expr_ref(m_util_s.str.mk_length(it->second), m);
                } else {
                    var_expr = expr_ref(mk_int_var(node.atom_val.get_name().encode(), m, m_util_s, m_util_a), m);
                }
                return var_expr;
            }

        case LenFormulaType::PLUS: {
            assert(node.succ.size() >= 2);
            expr_ref plus = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                plus = m_util_a.mk_add(plus, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return plus;
        }

        case LenFormulaType::EQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_eq(left, right), m);
        }

        case LenFormulaType::LEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_le(left, right), m);
        }

        case LenFormulaType::NOT: {
            assert(node.succ.size() == 1);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m.mk_not(left), m);
        }

        case LenFormulaType::AND: {
            if(node.succ.size() == 0)
                return expr_ref(m.mk_true(), m);
            expr_ref andref = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                andref = m.mk_and(andref, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return andref;
        }

        case LenFormulaType::TRUE: {
            return expr_ref(m.mk_true(), m);
        }

        case LenFormulaType::FALSE: {
            return expr_ref(m.mk_false(), m);
        }

        }

        assert(false);
        return {{}, m};
    }
}

#endif
