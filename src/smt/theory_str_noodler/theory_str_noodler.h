/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3.
Eternal glory to Yu-Fang.
*/

#ifndef _THEORY_STR_NOODLER_H_
#define _THEORY_STR_NOODLER_H_

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

#include <mata/nfa.hh>

#include "formula.h"
#include "inclusion_graph.h"
#include "decision_procedure.h"
#include "expr_solver.h"
#include "util.h"

namespace smt::noodler {

    class theory_str_noodler : public theory {
    protected:

        int m_scope_level = 0;
        static bool is_over_approximation;
        const theory_str_params& m_params;
        th_rewriter m_rewrite;
        arith_util m_util_a;
        seq_util m_util_s;
        //ast_manager& m;

        StateLen<bool> state_len;
        obj_hashtable<expr> len_vars;

        // mapping predicates and function to variables that they substitute to
        obj_map<expr, expr*> predicate_replace;

        obj_hashtable<expr> axiomatized_terms;
        obj_hashtable<expr> propgated_string_theory;
        obj_hashtable<expr> m_has_length;          // is length applied
        expr_ref_vector     m_length;             // length applications themselves

        vector<std::pair<obj_hashtable<expr>,std::vector<app_ref>>> len_state;
        obj_map<expr, unsigned> bool_var_int;
        obj_hashtable<expr> bool_var_state;

        std::set<std::pair<int,int>> axiomatized_eq_vars;
        using expr_pair = std::pair<expr_ref, expr_ref>;
        using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;
        using tvar_pair = std::pair<theory_var , theory_var >;

        scoped_vector<tvar_pair> m_word_eq_var_todo;
        scoped_vector<tvar_pair> m_word_diseq_var_todo;


        scoped_vector<expr_pair> m_word_eq_todo;
        scoped_vector<expr_pair> m_word_diseq_todo;
        scoped_vector<expr_pair> m_not_contains_todo;
        scoped_vector<expr_pair_flag> m_membership_todo;
        vector<expr_pair> m_word_eq_todo_rel;
        vector<expr_pair> m_word_diseq_todo_rel;
        vector<expr_pair_flag> m_membership_todo_rel;

    public:
        char const * get_name() const override { return "noodler"; }
        theory_str_noodler(context& ctx, ast_manager & m, theory_str_params const & params);
        void display(std::ostream& os) const override;
        theory *mk_fresh(context * newctx) override { return alloc(theory_str_noodler, *newctx, get_manager(), m_params); }
        void init() override;
        theory_var mk_var(enode *n) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        bool internalize_atom(app *atom, bool gate_ctx) override;
        bool internalize_term(app *term) override;
        void init_search_eh() override;
        void relevant_eh(app *n) override;
        void assign_eh(bool_var v, bool is_true) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void reset_eh() override;
        final_check_status final_check_eh() override;
        model_value_proc *mk_value(enode *n, model_generator& mg) override;
        void init_model(model_generator& m) override;
        void finalize_model(model_generator& mg) override;
        lbool validate_unsat_core(expr_ref_vector& unsat_core) override;

        void add_length_axiom(expr* n);

        expr_ref mk_str_var(symbol const&);
        enode* ensure_enode(expr* a);
        expr_ref mk_skolem(symbol const& s, expr *e1, expr *e2 = nullptr, expr *e3 = nullptr,
                           expr *e4 = nullptr, sort *sort = nullptr);
        expr_ref mk_len(expr* s) const { return expr_ref(m_util_s.str.mk_length(s), m); }

        void add_axiom(expr *e);
        void add_block_axiom(expr *const e);
        literal mk_eq_empty(expr* n, bool phase = true);
        expr_ref mk_last(expr* e);
        expr_ref mk_first(expr* e);
        expr_ref mk_concat(expr* e1, expr* e2);


        bool has_length(expr *e) const { return m_has_length.contains(e); }
        void add_length(expr* e);
        void enforce_length(expr* n);

        ~theory_str_noodler() {}

    protected:
        bool is_of_this_theory(expr *e) const;
        bool is_string_sort(expr *e) const;
        bool is_regex_sort(expr *e) const;
        bool is_const_fun(expr *e) const;
        expr_ref mk_sub(expr *a, expr *b);
        zstring print_word_term(expr * a) const;


        literal mk_literal(expr *e);
        bool_var mk_bool_var(expr *e);
        expr_ref mk_str_var(const std::string& name);
        expr_ref mk_int_var(const std::string& name);

        void add_axiom(std::initializer_list<literal> ls);
        void handle_char_at(expr *e);
        void handle_substr(expr *e);
        void handle_index_of(expr *e);
        void handle_replace(expr *e);
        void handle_prefix(expr *e);
        void handle_suffix(expr *e);
        void handle_not_prefix(expr *e);
        void handle_not_suffix(expr *e);
        void handle_contains(expr *e);
        void handle_not_contains(expr *e);
        void handle_in_re(expr *e, bool is_true);
        void set_conflict(const literal_vector& ls);
        void block_curr_assignment();
        void dump_assignments() const;
        void string_theory_propagation(expr * ex);
        void propagate_concat_axiom(enode * cat);
        void propagate_basic_string_axioms(enode * str);
        void tightest_prefix(expr*,expr*);
        void print_ast(expr *e);
        void print_ctx(context& ctx);

        void block_len(int n_cnt);
        void block_len_single(int n_cnt, const app_ref& bool_var, expr_ref& refine);

        void get_len_state_var(const obj_hashtable<expr>& conj, app_ref* bool_var);
        void update_len_state_var(const obj_hashtable<expr>& conj, const app_ref& bool_var);
        std::vector<app_ref> find_state_var(const obj_hashtable<expr>& conj);

        void remove_irrelevant_constr();

        Predicate conv_eq_pred(const app* expr);
        void conj_instance(const obj_hashtable<app>& conj, Formula &res);
    };
}

#endif /* _THEORY_STR_NOODLER_H_ */
