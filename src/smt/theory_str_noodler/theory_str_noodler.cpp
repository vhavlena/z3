/*
The skeleton of this code was obtained by Yu-Fang Chen from https://github.com/guluchen/z3. 
Eternal glory to Yu-Fang.
*/

#include <algorithm>
#include <sstream>
#include <iostream>
#include <cmath>
#include "ast/ast_pp.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/theory_lra.h"
#include "smt/theory_arith.h"
#include "smt/smt_context.h"
#include "ast/seq_decl_plugin.h"
#include "ast/reg_decl_plugins.h"


namespace smt::noodler {
    bool theory_str_noodler::is_over_approximation = false;

    namespace {
        bool IN_CHECK_FINAL = false;
    }

    theory_str_noodler::theory_str_noodler(context& ctx, ast_manager & m, theory_str_params const & params): 
        theory(ctx, ctx.get_manager().mk_family_id("seq")), 
        m_params(params),
        m_rewrite(m), 
        m_util_a(m),
        m_util_s(m),
        m_length(m)
        {}

    void theory_str_noodler::display(std::ostream &os) const {
        os << "theory_str display" << std::endl;
    }

    void theory_str_noodler::init() {
        theory::init();
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init\n";);
    }

    enode *theory_str_noodler::ensure_enode(expr *e) {
        context &ctx = get_context();
        if (!ctx.e_internalized(e)) {
            ctx.internalize(e, false);
        }
        enode *n = ctx.get_enode(e);
        ctx.mark_as_relevant(n);
        return n;
    }

    theory_var theory_str_noodler::mk_var(enode *const n) {
        if (!m_util_s.is_seq(n->get_expr()) &&
            !m_util_s.is_re(n->get_expr())) {
            return null_theory_var;
        }
        if (is_attached_to_var(n)) {
            return n->get_th_var(get_id());
        } else {
            theory_var v = theory::mk_var(n);
            get_context().attach_th_var(n, this, v);
            get_context().mark_as_relevant(n);
            return v;
        }
    }


    bool theory_str_noodler::internalize_atom(app *const atom, const bool gate_ctx) {
        (void) gate_ctx;
        STRACE("str", tout << "internalize_atom: gate_ctx is " << gate_ctx << ", "
                           << mk_pp(atom, get_manager()) << '\n';);
        context &ctx = get_context();
        if (ctx.b_internalized(atom)) {
            STRACE("str", tout << "done before\n";);
            return true;
        }
        return internalize_term(atom);
    }

    bool theory_str_noodler::internalize_term(app *const term) {
        context &ctx = get_context();

        if (m_util_s.str.is_in_re(term)) {
            if (!ctx.e_internalized(term->get_arg(0))) {
                ctx.internalize(term->get_arg(0), false);
                enode* enode = ctx.get_enode(term->get_arg(0));
                mk_var(enode);
            }
        }

        if (ctx.e_internalized(term)) {
            enode *e = ctx.get_enode(term);
            mk_var(e);
            return true;
        }
        for (auto arg : *term) {
            mk_var(ensure_enode(arg));
        }
        if (m.is_bool(term)) {
            bool_var bv = ctx.mk_bool_var(term);
            ctx.set_var_theory(bv, get_id());
            //We do not want to mark as relevant because it involves 
            // irrelevant RE solutions comming from the underlying SAT solver.
            //ctx.mark_as_relevant(bv);
        }

        enode *e = nullptr;
        if (ctx.e_internalized(term)) {
            e = ctx.get_enode(term);
        } else {
            e = ctx.mk_enode(term, false, m.is_bool(term), true);
        }
        mk_var(e);
        if (!ctx.relevancy()) {
            relevant_eh(term);
        }
        return true;
    }

    void theory_str_noodler::apply_sort_cnstr(enode *n, sort *s) {
        mk_var(n);
    }

    void theory_str_noodler::print_ctx(context &ctx) {  // test_hlin
        ast_manager m = get_manager();
        expr_ref_vector dis(m);
        expr_ref_vector vars(m);
        expr_ref_vector cons(m);
        expr_ref_vector unfixed(m);

        expr_ref_vector con(get_manager());
        expr_ref_vector un(get_manager());

        ctx.get_assignments(con);
        std::cout << "Assignment :" << con.size() << " " << un.size() << std::endl;
        for(expr* e : con) {
            std::cout << "OOO " << mk_pp(e, m) << " " << ctx.is_relevant(e) << " " << ctx.b_internalized(e) << " " << ctx.find_assignment(e);
            if(ctx.b_internalized(e)) {
                std::cout << ctx.get_bool_var(e);
            }
            std::cout << std::endl;
        }

        return;
        
        std::cout << ctx.get_unsat_core_size() << std::endl;
        std::cout << "~~~~~ print ctx start ~~~~~~~\n";
//        context& ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        expr_ref_vector Literals(get_manager()), Assigns(get_manager());
        ctx.get_guessed_literals(Literals);
        ctx.get_assignments(Assigns);
        std::cout << "~~~~~~ from get_asserted_formulas ~~~~~~\n";
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            std::cout << mk_pp(ex, get_manager()) << " relevant? " << ctx.is_relevant(ex) << std::endl;
        }
        std::cout << "~~~~~~ from get_guessed_literals ~~~~~~\n";
        for (auto &e : Literals) {
            std::cout << mk_pp(e, get_manager()) << " relevant? " << ctx.is_relevant(e) << std::endl;
        }
        std::cout << "~~~~~~ from get_assignments ~~~~~~\n";
        for (auto &e : Assigns) {
//            print_ast(e);
            std::cout << mk_pp(e, get_manager()) << " relevant? " << ctx.is_relevant(e) << std::endl;
        }
        std::cout << "~~~~~ print ctx end ~~~~~~~~~\n";
    }

    void theory_str_noodler::print_ast(expr *e) {  // test_hlin
        ast_manager m = get_manager();
        unsigned int id = e->get_id();
        ast_kind ast = e->get_kind();
        sort *e_sort = e->get_sort();
        sort *bool_sort = m.mk_bool_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();
        std::cout << "#e.id = " << id << std::endl;
        std::cout << "#e.kind = " << get_ast_kind_name(ast) << std::endl;
        std::cout << std::boolalpha << "#is bool sort? " << (e_sort == bool_sort) << std::endl;
        std::cout << std::boolalpha << "#is string sort? " << (e_sort == str_sort) << std::endl;
        std::cout << std::boolalpha << "#is string term? " << m_util_s.str.is_string(e) << std::endl;
        std::cout << std::boolalpha << "#is_numeral? " << m_util_a.is_numeral(e) << std::endl;
        std::cout << std::boolalpha << "#is_to_int? " << m_util_a.is_to_int(e) << std::endl;
        std::cout << std::boolalpha << "#is_int_expr? " << m_util_a.is_int_expr(e) << std::endl;
        std::cout << std::boolalpha << "#is_le? " << m_util_a.is_le(e) << std::endl;
        std::cout << std::boolalpha << "#is_ge? " << m_util_a.is_ge(e) << std::endl;
    }


    void theory_str_noodler::init_search_eh() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        unsigned nFormulas = ctx.get_num_asserted_formulas();
        for (unsigned i = 0; i < nFormulas; ++i) {
            expr *ex = ctx.get_asserted_formula(i);
            string_theory_propagation(ex);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::string_theory_propagation(expr *expr) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        STRACE("str", tout << mk_pp(expr, get_manager()) << std::endl;);

        context &ctx = get_context();

        if (!ctx.e_internalized(expr)) {
            ctx.internalize(expr, false);
        }
        //We do not mark the expression as relevant since we do not want bias a 
        //fresh SAT solution by the newly added theory axioms. 
        //enode *n = ctx.get_enode(expr);
        //ctx.mark_as_relevant(n);

        sort *expr_sort = expr->get_sort();
        sort *str_sort = m_util_s.str.mk_string_sort();

        if (expr_sort == str_sort) {

            enode *n = ctx.get_enode(expr);
            propagate_basic_string_axioms(n);
            if (is_app(expr) && m_util_s.str.is_concat(to_app(expr))) {
                propagate_concat_axiom(n);
            }
        }
        // if expr is an application, recursively inspect all arguments
        if (is_app(expr) && !m_util_s.str.is_length(expr)) {
            app *term = to_app(expr);
            unsigned num_args = term->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                string_theory_propagation(term->get_arg(i));
            }
        }

        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::propagate_concat_axiom(enode *cat) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen = false;


        app *a_cat = cat->get_expr();
        SASSERT(m_util_s.str.is_concat(a_cat));
        ast_manager &m = get_manager();

        // build LHS
        expr_ref len_xy(m);
        len_xy = m_util_s.str.mk_length(a_cat);
        SASSERT(len_xy);

        // build RHS: start by extracting x and y from Concat(x, y)
        SASSERT(a_cat->get_num_args() == 2);
        app *a_x = to_app(a_cat->get_arg(0));
        app *a_y = to_app(a_cat->get_arg(1));
        expr_ref len_x(m);
        len_x = m_util_s.str.mk_length(a_x);
        SASSERT(len_x);

        expr_ref len_y(m);
        len_y = m_util_s.str.mk_length(a_y);
        SASSERT(len_y);

        // now build len_x + len_y
        expr_ref len_x_plus_len_y(m);
        len_x_plus_len_y = m_util_a.mk_add(len_x, len_y);
        SASSERT(len_x_plus_len_y);

        if (on_screen)
            std::cout << "[Concat Axiom] " << mk_pp(len_xy, m) << " = " << mk_pp(len_x, m) << " + " << mk_pp(len_y, m)
                      << std::endl;

        // finally assert equality between the two subexpressions
        app *eq = m.mk_eq(len_xy, len_x_plus_len_y);
        SASSERT(eq);
        add_axiom(eq);
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::propagate_basic_string_axioms(enode *str) {
        bool on_screen = false;

        return; 

        context &ctx = get_context();
        ast_manager &m = get_manager();

        {
            sort *a_sort = str->get_expr()->get_sort();
            sort *str_sort = m_util_s.str.mk_string_sort();
            if (a_sort != str_sort) {
                STRACE("str",
                       tout << "WARNING: not setting up string axioms on non-string term " << mk_pp(str->get_expr(), m)
                            << std::endl;);
                return;
            }
        }

        // TESTING: attempt to avoid a crash here when a variable goes out of scope
        if (str->get_iscope_lvl() > ctx.get_scope_level()) {
            STRACE("str", tout << "WARNING: skipping axiom setup on out-of-scope string term" << std::endl;);
            return;
        }

        // generate a stronger axiom for constant strings
        app *a_str = str->get_expr();

        if (m_util_s.str.is_string(a_str)) {
            if (on_screen) std::cout << "[ConstStr Axiom] " << mk_pp(a_str, m) << std::endl;

            expr_ref len_str(m);
            len_str = m_util_s.str.mk_length(a_str);
            SASSERT(len_str);

            zstring strconst;
            m_util_s.str.is_string(str->get_expr(), strconst);
            unsigned int l = strconst.length();
            expr_ref len(m_util_a.mk_numeral(rational(l), true), m);

            literal lit(mk_eq(len_str, len, false));
            ctx.mark_as_relevant(lit);
            ctx.mk_th_axiom(get_id(), 1, &lit);
        } else {
            // build axiom 1: Length(a_str) >= 0
            {
                if (on_screen) std::cout << "[Non-Zero Axiom] " << mk_pp(a_str, m) << std::endl;

                // build LHS
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                // build RHS
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                // build LHS >= RHS and assert
                app *lhs_ge_rhs = m_util_a.mk_ge(len_str, zero);
                SASSERT(lhs_ge_rhs);
                STRACE("str", tout << "string axiom 1: " << mk_ismt2_pp(lhs_ge_rhs, m) << std::endl;);
                add_axiom(lhs_ge_rhs);
            }

            // build axiom 2: Length(a_str) == 0 <=> a_str == ""
            {
                if (on_screen) std::cout << "[Zero iff Empty Axiom] " << mk_pp(a_str, m) << std::endl;

                // build LHS of iff
                expr_ref len_str(m);
                len_str = m_util_s.str.mk_length(a_str);
                SASSERT(len_str);
                expr_ref zero(m);
                zero = m_util_a.mk_numeral(rational(0), true);
                SASSERT(zero);
                expr_ref lhs(m);
                lhs = ctx.mk_eq_atom(len_str, zero);
                SASSERT(lhs);
                // build RHS of iff
                expr_ref empty_str(m);
                empty_str = m_util_s.str.mk_string(zstring(""));
                SASSERT(empty_str);
                expr_ref rhs(m);
                rhs = ctx.mk_eq_atom(a_str, empty_str);
                SASSERT(rhs);
                // build LHS <=> RHS and assert
                literal l(mk_eq(lhs, rhs, true));
                ctx.mark_as_relevant(l);
                ctx.mk_th_axiom(get_id(), 1, &l);
            }

        }
    }

    void theory_str_noodler::add_length_axiom(expr *n) {
        add_axiom(m_util_a.mk_ge(n, m_util_a.mk_int(0)));

    }

    void theory_str_noodler::relevant_eh(app *const n) {
        STRACE("str", tout << "relevant: " << mk_pp(n, get_manager()) << '\n';);

        if (m_util_s.str.is_length(n)) {
            add_length_axiom(n);
        }
        if (m_util_s.str.is_extract(n)) {
            std::cout << "substr" << std::endl;
            handle_substr(n);
        } else if (m_util_s.str.is_itos(n)) {
            //handle_itos(n);
        } else if (m_util_s.str.is_stoi(n)) {
            //handle_stoi(n);
        } else if (m_util_s.str.is_at(n)) {
            handle_char_at(n);
        } else if (m_util_s.str.is_replace(n)) {
            handle_replace(n);
        } else if (m_util_s.str.is_index(n)) {
            handle_index_of(n);
        }

        expr *arg;
        if (m_util_s.str.is_length(n, arg) && !has_length(arg) && get_context().e_internalized(arg)) {
            enforce_length(arg);
        }

    }

    /*
    ensure that all elements in equivalence class occur under an application of 'length'
    */
    void theory_str_noodler::enforce_length(expr *e) {
        enode *n = ensure_enode(e);
        enode *n1 = n;
        do {
            expr *o = n->get_expr();
            if (!has_length(o)) {
                expr_ref len = mk_len(o);
                add_length_axiom(len);
            }
            n = n->get_next();
        } while (n1 != n);
    }

    void theory_str_noodler::assign_eh(bool_var v, const bool is_true) {
        ast_manager &m = get_manager();
        STRACE("str", tout << "assign: bool_var #" << v << " is " << is_true << ", "
                            << mk_pp(get_context().bool_var2expr(v), m) << "@ scope level:" << m_scope_level << '\n';);
        context &ctx = get_context();
        expr *e = ctx.bool_var2expr(v);
        expr *e1 = nullptr, *e2 = nullptr;
        if (m_util_s.str.is_prefix(e, e1, e2)) {
            if (is_true) {
                handle_prefix(e);
            } else {
                handle_not_prefix(e);
            }
        } else if (m_util_s.str.is_suffix(e, e1, e2)) {
            if (is_true) {
                handle_suffix(e);
            } else {
                handle_not_suffix(e);
            }
        } else if (m_util_s.str.is_contains(e, e1, e2)) {
            if (is_true) {
                handle_contains(e);
            } else {
                m_not_contains_todo.push_back({{e1, m},
                                               {e2, m}});
            }
        } else if (m_util_s.str.is_in_re(e)) {
            handle_in_re(e, is_true);
        } else {
            TRACE("str", tout << "unhandled literal " << mk_pp(e, m) << "\n";);
            UNREACHABLE();
        }
    }

    void theory_str_noodler::new_eq_eh(theory_var x, theory_var y) {
        m_word_eq_var_todo.push_back({x, y});

        const expr_ref l{get_enode(x)->get_expr(), m};
        const expr_ref r{get_enode(y)->get_expr(), m};

        if (axiomatized_eq_vars.count(std::make_pair(x, y)) == 0) {
            axiomatized_eq_vars.insert(std::make_pair(x, y));


            literal l_eq_r = mk_eq(l, r, false);
            literal len_l_eq_len_r = mk_eq(m_util_s.str.mk_length(l), m_util_s.str.mk_length(r), false);
            add_axiom({~l_eq_r, len_l_eq_len_r});
        }
        m_word_eq_todo.push_back({l, r});
        STRACE("str", tout << "new_eq: " << l << " = " << r << '\n';);
    }

    template<class T>
    static T *get_th_arith(context &ctx, theory_id afid, expr *e) {
        theory *th = ctx.get_theory(afid);
        if (th && ctx.e_internalized(e)) {
            return dynamic_cast<T *>(th);
        } else {
            return nullptr;
        }
    }

    void theory_str_noodler::new_diseq_eh(theory_var x, theory_var y) {
        ast_manager &m = get_manager();
        const expr_ref l{get_enode(x)->get_expr(), m};
        const expr_ref r{get_enode(y)->get_expr(), m};

        m_word_diseq_var_todo.push_back({x, y});
        m_word_diseq_todo.push_back({l, r});    
        
        app_ref l_eq_r(ctx.mk_eq_atom(l.get(), r.get()), m);
        app_ref neg(m.mk_not(l_eq_r), m);
        ctx.internalize(neg, false);

        STRACE("str", tout << ctx.find_assignment(l_eq_r.get()) << " " << ctx.find_assignment(neg.get()) << '\n';);
        STRACE("str", tout << "new_diseq: " << l << " != " << r << " @" << m_scope_level<< " " << ctx.get_bool_var(l_eq_r.get()) << " " << ctx.get_bool_var(neg) << '\n';);
    }

    bool theory_str_noodler::can_propagate() {
        return false;
    }

    void theory_str_noodler::propagate() {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "o propagate" << '\n';);
    }

    void theory_str_noodler::push_scope_eh() {
        m_scope_level += 1;
        m_word_eq_todo.push_scope();
        m_word_diseq_todo.push_scope();
        m_word_eq_var_todo.push_scope();
        m_word_diseq_var_todo.push_scope();
        m_membership_todo.push_scope();
        m_not_contains_todo.push_scope();
        STRACE("str", if (!IN_CHECK_FINAL) tout << "push_scope: " << m_scope_level << '\n';);
    }

    void theory_str_noodler::pop_scope_eh(const unsigned num_scopes) {
        m_scope_level -= num_scopes;
        m_word_eq_todo.pop_scope(num_scopes);
        m_word_diseq_todo.pop_scope(num_scopes);
        m_word_eq_var_todo.pop_scope(num_scopes);
        m_word_diseq_var_todo.pop_scope(num_scopes);
        m_membership_todo.pop_scope(num_scopes);
        m_not_contains_todo.pop_scope(num_scopes);
        m_rewrite.reset();
        STRACE("str", if (!IN_CHECK_FINAL)
            tout << "pop_scope: " << num_scopes << " (back to level " << m_scope_level << ")\n";);
    }

    void theory_str_noodler::reset_eh() {
        STRACE("str", tout << "reset" << '\n';);
    }



    zstring theory_str_noodler::print_word_term(expr * e) const{
        zstring s;
        if (m_util_s.str.is_string(e, s)) {
            return s;
        }
        if (m_util_s.str.is_concat(e)) {
            //e is a concat of some elements
            for (unsigned i = 0; i < to_app(e)->get_num_args(); i++) {
                s = s+ print_word_term(to_app(e)->get_arg(i));
            }
            return s;
        }
        if (m_util_s.str.is_stoi(e)){
            return zstring("stoi");
        }
        if (m_util_s.str.is_itos(e)){
            return zstring("itos");
        }

        // e is a string variable
        std::stringstream ss;
        ss << "V("<<mk_pp(e, get_manager())<<")";
        s = zstring(ss.str().data());
        return s;

    }

    /**
    Remove irrelevant string constraints. In particular remove equations, disequations, and 
    regular constraints that are not relevant for SAT checking.
    */
    void theory_str_noodler::remove_irrelevant_constr() {
        
        this->m_word_eq_todo_rel.clear();
        this->m_word_diseq_todo_rel.clear();
        this->m_membership_todo_rel.clear();

        for (const auto& we : m_word_eq_todo) {
            app_ref eq(ctx.mk_eq_atom(we.first, we.second), m);
            if(!ctx.is_relevant(eq.get())) {
                STRACE("str", tout << "remove_irrelevant_eqs: " << mk_pp(eq.get(), m) << " relevant: " << 
                    ctx.is_relevant(eq.get()) << " assign: " << ctx.find_assignment(eq.get()) << '\n';);
                continue;
            }   

            // app_ref double_not(m.mk_not(m.mk_not(eq)), m);
            // ctx.internalize(double_not, false);
            // if(ctx.find_assignment(double_not.get()) != l_undef && !ctx.is_relevant(double_not.get())) {
            //     STRACE("str", tout << "remove_irrelevant_eqs: " << mk_pp(double_not.get(), m) << " relevant: " << 
            //         ctx.is_relevant(double_not.get()) << " assign: " << ctx.find_assignment(double_not.get()) << '\n';);
            //     continue;
            // }

            this->m_word_eq_todo_rel.push_back(we);
        }

        for (const auto& we : m_word_diseq_todo) {
            app_ref eq(ctx.mk_eq_atom(we.first, we.second), m);
            app_ref dis(m.mk_not(eq), m);
            if(!ctx.is_relevant(dis.get())) {
                STRACE("str", tout << "remove_irrelevant_eqs: " << mk_pp(dis.get(), m) << " relevant: " << 
                    ctx.is_relevant(dis.get()) << " assign: " << ctx.find_assignment(dis.get()) << '\n';);
                continue;
            }
            this->m_word_diseq_todo_rel.push_back(we);
        }

        for (const auto& we : this->m_membership_todo) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(we), std::get<1>(we)), m);
            if(!std::get<2>(we)){
                in_app = m.mk_not(in_app);
            }
            if(ctx.is_relevant(in_app.get())) {
                STRACE("str", tout << "remove_irrelevant_eqs: " << mk_pp(in_app.get(), m) << " relevant: " << 
                    ctx.is_relevant(in_app.get()) << " assign: " << ctx.find_assignment(in_app.get()) << '\n';);
                this->m_membership_todo_rel.push_back(we);
                continue;
            }
        }
    }

    /*
    Final check for an assignment of the underlying boolean skeleton.
    */
    final_check_status theory_str_noodler::final_check_eh() {
        TRACE("str",  tout << "pop_scope: ";);
        std::cout << "final_check starts\n"<<std::endl;

        //print_ctx(get_context());

        // if (m_word_eq_todo.empty()) {
        //     if (is_over_approximation)
        //         return FC_GIVEUP;
        //     else
        //         return FC_DONE;
        // }

        remove_irrelevant_constr();

        obj_hashtable<expr> conj;
        obj_hashtable<app> conj_instance;

        for (const auto& we : this->m_word_eq_todo_rel) {

            app *const e = ctx.mk_eq_atom(we.first, we.second);
            conj.insert(e);
            conj_instance.insert(e);

            std::cout<<print_word_term(we.first) <<std::flush;
            std::cout<<"="<<std::flush;
            std::cout<<print_word_term(we.second) << std::endl;
        }

        for (const auto& we : this->m_word_diseq_todo_rel) {
            app *const e = m.mk_not(ctx.mk_eq_atom(we.first, we.second));
            conj_instance.insert(e);

            std::cout<<print_word_term(we.first) <<std::flush;
            std::cout<<"!="<<std::flush;
            std::cout<<print_word_term(we.second)<< std::endl;
        }

        ast_manager &m = get_manager();
        for (const auto& we : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(we), std::get<1>(we)), m);
            if(!std::get<2>(we)){
                in_app = m.mk_not(in_app);
            }
            std::cout << mk_pp(std::get<0>(we), m) << " in RE" << std::endl;

        }

        Formula instance;
        this->conj_instance(conj_instance, instance);

        bool found = false;
        int n_cnt = -1;
        for(const auto& pr : this->visited) {
            for(auto* const ex : conj) {
                found = false;
                if(!pr.first.contains(ex)) {
                    break;
                }
                found = true;
            }
            if(found) {
                n_cnt = pr.second;
                break;
            }
        }

        if(n_cnt == -1) {
            n_cnt = this->cnt;
            std::cout << "not visited" << std::endl;
        }
        this->visited.push_back({conj, n_cnt});

        block_len(n_cnt);
        this->cnt = fmax(this->cnt, n_cnt + 3);
        return FC_DONE;


        block_curr_assignment();
        TRACE("str", tout << "final_check ends\n";);
        IN_CHECK_FINAL = false;
        
        return FC_CONTINUE;
    }

    model_value_proc *theory_str_noodler::mk_value(enode *const n, model_generator &mg) {
        app *const tgt = n->get_expr();
        (void) m;
        STRACE("str", tout << "mk_value: sort is " << mk_pp(tgt->get_sort(), m) << ", "
                           << mk_pp(tgt, m) << '\n';);
        return alloc(expr_wrapper_proc, tgt);
    }

    void theory_str_noodler::init_model(model_generator &mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "init_model\n";);
    }

    void theory_str_noodler::finalize_model(model_generator &mg) {
        STRACE("str", if (!IN_CHECK_FINAL) tout << "finalize_model\n";);
    }

    lbool theory_str_noodler::validate_unsat_core(expr_ref_vector &unsat_core) {
        return l_undef;
    }

    bool theory_str_noodler::is_of_this_theory(expr *const e) const {
        return is_app(e) && to_app(e)->get_family_id() == get_family_id();
    }

    bool theory_str_noodler::is_string_sort(expr *const e) const {
        return m_util_s.str.is_string_term(e);
    }

    bool theory_str_noodler::is_regex_sort(expr *const e) const {
        return m_util_s.is_re(e);
    }

    bool theory_str_noodler::is_const_fun(expr *const e) const {
        return is_app(e) && to_app(e)->get_decl()->get_arity() == 0;
    }

    expr_ref theory_str_noodler::mk_sub(expr *a, expr *b) {
        ast_manager &m = get_manager();

        expr_ref result(m_util_a.mk_sub(a, b), m);
        m_rewrite(result);
        return result;
    }


    expr_ref
    theory_str_noodler::mk_skolem(symbol const &name, expr *e1, expr *e2, expr *e3, expr *e4, sort *sort) {
        ast_manager &m = get_manager();
        expr *es[4] = {e1, e2, e3, e4};
        unsigned len = e4 ? 4 : (e3 ? 3 : (e2 ? 2 : 1));

        if (!sort) {
            sort = e1->get_sort();
        }
        app *a = m_util_s.mk_skolem(name, len, es, sort);

//        ctx.internalize(a, false);
//        mk_var(ctx.get_enode(a));
//        propagate_basic_string_axioms(ctx.get_enode(a));
//
//        enode* n = ctx.get_enode(a);
//
//        if (!is_attached_to_var(n)) {
//            const theory_var v = theory::mk_var(n);
//            ctx.attach_th_var(n, this, v);
//            ctx.mark_as_relevant(n);
//            STRACE("str", tout << "new theory_var #" << v << '\n';);
//        }

        expr_ref ret(a, m);
        string_theory_propagation(ret);

        return expr_ref(a, m);

    }

    literal theory_str_noodler::mk_literal(expr *const e) {
        ast_manager &m = get_manager();
        context &ctx = get_context();
        expr_ref ex{e, m};
        m_rewrite(ex);
        if (!ctx.e_internalized(ex)) {
            ctx.internalize(ex, false);
        }
        enode *const n = ctx.get_enode(ex);
        ctx.mark_as_relevant(n);
        return ctx.get_literal(ex);
    }

    bool_var theory_str_noodler::mk_bool_var(expr *const e) {
        ast_manager &m = get_manager();
        STRACE("str", tout << "mk_bool_var: " << mk_pp(e, m) << '\n';);
        if (!m.is_bool(e)) {
            return null_bool_var;
        }
        context &ctx = get_context();
        SASSERT(!ctx.b_internalized(e));
        const bool_var &bv = ctx.mk_bool_var(e);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
        return bv;
    }

    void theory_str_noodler::add_block_axiom(expr *const e) {
        STRACE("str", tout <<  __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

        if (!axiomatized_terms.contains(e) || false) {
            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
            context &ctx = get_context();
            if (!ctx.b_internalized(e)) {
                ctx.internalize(e, false);
            }
            ctx.internalize(e, false);
            literal l{ctx.get_literal(e)};
            ctx.mk_th_axiom(get_id(), 1, &l);
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e] block: \n", l) << '\n';);
        }
    }

    void theory_str_noodler::add_axiom(expr *const e) {
        bool on_screen = true;
        STRACE("str_axiom", tout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);

        if (on_screen) STRACE("str_axiom",
                              std::cout << __LINE__ << " " << __FUNCTION__ << mk_pp(e, get_manager()) << std::endl;);


        if (!axiomatized_terms.contains(e) || false) {
            axiomatized_terms.insert(e);
            if (e == nullptr || get_manager().is_true(e)) return;
//        string_theory_propagation(e);
            context &ctx = get_context();
//        SASSERT(!ctx.b_internalized(e));
            if (!ctx.b_internalized(e)) {
                ctx.internalize(e, false);
            }
            ctx.internalize(e, false);
            literal l{ctx.get_literal(e)};
            ctx.mark_as_relevant(l);
            ctx.mk_th_axiom(get_id(), 1, &l);
            STRACE("str", ctx.display_literal_verbose(tout << "[Assert_e]\n", l) << '\n';);
        }
    }

    void theory_str_noodler::add_axiom(std::initializer_list<literal> ls) {
        bool on_screen = true;

        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);
        context &ctx = get_context();
        literal_vector lv;
        for (const auto &l : ls) {
            if (l != null_literal && l != false_literal) {
                ctx.mark_as_relevant(l);
                lv.push_back(l);
            }
        }
        ctx.mk_th_axiom(get_id(), lv, lv.size());
        if (on_screen) STRACE("str_axiom", std::cout << __LINE__ << " " << __FUNCTION__;);
        if (on_screen) STRACE("str_axiom", ctx.display_literals_verbose(std::cout, lv) << std::endl;);
        STRACE("str_axiom", ctx.display_literals_verbose(tout << "[Assert_c]\n", lv) << '\n';);
        STRACE("str_axiom", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      Let e = at(s, i)
        0 <= i < len(s)  ->  s = xey /\ len(x) = i /\ len(e) = 1
        i < 0 \/ i >= len(s)  ->  e = empty
    */
    void theory_str_noodler::handle_char_at(expr *e) {

        ast_manager &m = get_manager();
        expr *s = nullptr, *i = nullptr;
        VERIFY(m_util_s.str.is_at(e, s, i));
        expr_ref len_e(m_util_s.str.mk_length(e), m);
        expr_ref len_s(m_util_s.str.mk_length(s), m);
        expr_ref zero(m_util_a.mk_int(0), m);
        expr_ref one(m_util_a.mk_int(1), m);
        expr_ref x = mk_skolem(symbol("m_char_at_left"), s, i);
        expr_ref y = mk_skolem(symbol("m_char_at_right"), s, i);
        expr_ref xey(m_util_s.str.mk_concat(x, m_util_s.str.mk_concat(e, y)), m);
        string_theory_propagation(xey);

        expr_ref len_x(m_util_s.str.mk_length(x), m);
        expr_ref emp(m_util_s.str.mk_empty(e->get_sort()), m);

        literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
        literal i_ge_len_s = mk_literal(m_util_a.mk_ge(mk_sub(i, m_util_s.str.mk_length(s)), zero));

        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(s, xey, false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(one, len_e, false)});
        add_axiom({~i_ge_0, i_ge_len_s, mk_eq(i, len_x, false)});

        add_axiom({i_ge_0, mk_eq(e, emp, false)});
        add_axiom({~i_ge_len_s, mk_eq(e, emp, false)});
    }

    /*
      Note: this is copied and modified from theory_seq.cpp
      TBD: check semantics of extract, a.k.a, substr(s, i ,l)

      let e = extract(s, i, l)

      i is start index, l is length of substring starting at index.

      i < 0 => e = ""
      i >= |s| => e = ""
      l <= 0 => e = ""
      0 <= i < |s| & l > 0 => s = xey, |x| = i, |e| = min(l, |s|-i)

    this translates to:

      0 <= i <= |s| -> s = xey
      0 <= i <= |s| -> len(x) = i
      0 <= i <= |s| & 0 <= l <= |s| - i -> |e| = l
      0 <= i <= |s| & |s| < l + i  -> |e| = |s| - i
      i >= |s| => |e| = 0
      i < 0 => |e| = 0
      l <= 0 => |e| = 0

      It follows that:
      |e| = min(l, |s| - i) for 0 <= i < |s| and 0 < |l|
    */
    void theory_str_noodler::handle_substr(expr *e) {
        if (!axiomatized_terms.contains(e) || false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *s = nullptr, *i = nullptr, *l = nullptr;
            VERIFY(m_util_s.str.is_extract(e, s, i, l));

            expr_ref x(mk_skolem(symbol("m_substr_left"), s, i), m);
            expr_ref ls(m_util_s.str.mk_length(s), m);
            expr_ref lx(m_util_s.str.mk_length(x), m);
            expr_ref le(m_util_s.str.mk_length(e), m);
            expr_ref ls_minus_i_l(mk_sub(mk_sub(ls, i), l), m);
            expr_ref y(mk_skolem(symbol("m_substr_right"), s, ls_minus_i_l), m);
            expr_ref xe(m_util_s.str.mk_concat(x, e), m);
            expr_ref xey(m_util_s.str.mk_concat(x, e, y), m);

            string_theory_propagation(xe);
            string_theory_propagation(xey);

            expr_ref zero(m_util_a.mk_int(0), m);

            literal i_ge_0 = mk_literal(m_util_a.mk_ge(i, zero));
            literal ls_le_i = mk_literal(m_util_a.mk_le(mk_sub(i, ls), zero));
            literal li_ge_ls = mk_literal(m_util_a.mk_ge(ls_minus_i_l, zero));
            literal l_ge_zero = mk_literal(m_util_a.mk_ge(l, zero));
            literal ls_le_0 = mk_literal(m_util_a.mk_le(ls, zero));

            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(xey, s, false)});
            add_axiom({~i_ge_0, ~ls_le_i, mk_eq(lx, i, false)});
            add_axiom({~i_ge_0, ~ls_le_i, ~l_ge_zero, ~li_ge_ls, mk_eq(le, l, false)});
            add_axiom({~i_ge_0, ~ls_le_i, li_ge_ls, mk_eq(le, mk_sub(ls, i), false)});
            add_axiom({~i_ge_0, ~ls_le_i, l_ge_zero, mk_eq(le, zero, false)});
            add_axiom({i_ge_0, mk_eq(le, zero, false)});
            add_axiom({ls_le_i, mk_eq(le, zero, false)});
            add_axiom({~ls_le_0, mk_eq(le, zero, false)});
        }
    }
    void theory_str_noodler::handle_replace(expr *r) {
        context& ctx = get_context();
        expr* a = nullptr, *s = nullptr, *t = nullptr;
        VERIFY(m_util_s.str.is_replace(r, a, s, t));
        expr_ref x  = mk_skolem(symbol("m_contains_left"), a, s);
        expr_ref y  = mk_skolem(symbol("m_contains_right"), a, s);
        expr_ref xty = mk_concat(x, mk_concat(t, y));
        expr_ref xsy = mk_concat(x, mk_concat(s, y));
        literal a_emp = mk_eq_empty(a, true);
        literal s_emp = mk_eq_empty(s, true);
        literal cnt = mk_literal(m_util_s.str.mk_contains(a, s));
        add_axiom({~a_emp, s_emp, mk_eq(r, a,false)});
        add_axiom({cnt,  mk_eq(r, a,false)});
        add_axiom({~s_emp, mk_eq(r, mk_concat(t, a),false)});
        add_axiom({~cnt, a_emp, s_emp, mk_eq(a, xsy,false)});
        add_axiom({~cnt, a_emp, s_emp, mk_eq(r, xty,false)});
        ctx.force_phase(cnt);
        tightest_prefix(s, x);

    }
    void theory_str_noodler::handle_index_of(expr *i) {
        if(!axiomatized_terms.contains(i)||false) {
            axiomatized_terms.insert(i);
            ast_manager &m = get_manager();
            expr *s = nullptr, *t = nullptr, *offset = nullptr;
            rational r;
            VERIFY(m_util_s.str.is_index(i, t, s) || m_util_s.str.is_index(i, t, s, offset));

            expr_ref minus_one(m_util_a.mk_int(-1), m);
            expr_ref zero(m_util_a.mk_int(0), m);

            expr_ref emp(m_util_s.str.mk_empty(t->get_sort()), m);

            literal cnt = mk_literal(m_util_s.str.mk_contains(t, s));


            literal i_eq_m1 = mk_eq(i, minus_one, false);
            literal i_eq_0 = mk_eq(i, zero, false);
            literal s_eq_empty = mk_eq(s, emp, false);
            literal t_eq_empty = mk_eq(t, emp, false);

            add_axiom({cnt, i_eq_m1});
            add_axiom({~t_eq_empty, s_eq_empty, i_eq_m1});

            if (!offset || (m_util_a.is_numeral(offset, r) && r.is_zero())) {
                expr_ref x = mk_skolem(symbol("m_contains_left"), t, s);
                expr_ref y = mk_skolem(symbol("m_contains_right"), t, s);
                expr_ref xsy(m_util_s.str.mk_concat(x, s, y), m);
                string_theory_propagation(xsy);

                // |s| = 0 => indexof(t,s,0) = 0
                // contains(t,s) & |s| != 0 => t = xsy & indexof(t,s,0) = |x|
                expr_ref lenx(m_util_s.str.mk_length(x), m);
                add_axiom({~s_eq_empty, i_eq_0});
                add_axiom({~cnt, s_eq_empty, mk_eq(t, xsy, false)});
                add_axiom({~cnt, s_eq_empty, mk_eq(i, lenx, false)});
                add_axiom({~cnt, mk_literal(m_util_a.mk_ge(i, zero))});

                tightest_prefix(s, x);
            } else {
                expr_ref len_t(m_util_s.str.mk_length(t), m);
                literal offset_ge_len = mk_literal(m_util_a.mk_ge(mk_sub(offset, len_t), zero));
                literal offset_le_len = mk_literal(m_util_a.mk_le(mk_sub(offset, len_t), zero));
                literal i_eq_offset = mk_eq(i, offset, false);
                add_axiom({~offset_ge_len, s_eq_empty, i_eq_m1});
                add_axiom({offset_le_len, i_eq_m1});
                add_axiom({~offset_ge_len, ~offset_le_len, ~s_eq_empty, i_eq_offset});

                expr_ref x = mk_skolem(symbol("m_contains_left"), t, s, offset);
                expr_ref y = mk_skolem(symbol("m_contains_right"), t, s, offset);
                expr_ref xy(m_util_s.str.mk_concat(x, y), m);
                string_theory_propagation(xy);

                expr_ref indexof0(m_util_s.str.mk_index(y, s, zero), m);
                expr_ref offset_p_indexof0(m_util_a.mk_add(offset, indexof0), m);
                literal offset_ge_0 = mk_literal(m_util_a.mk_ge(offset, zero));
                add_axiom(
                        {~offset_ge_0, offset_ge_len, mk_eq(t, xy, false)});
                add_axiom(
                        {~offset_ge_0, offset_ge_len, mk_eq(m_util_s.str.mk_length(x), offset, false)});
                add_axiom({~offset_ge_0, offset_ge_len, ~mk_eq(indexof0, minus_one, false), i_eq_m1});
                add_axiom({~offset_ge_0, offset_ge_len, ~mk_literal(m_util_a.mk_ge(indexof0, zero)),
                            mk_eq(offset_p_indexof0, i, false)});

                // offset < 0 => -1 = i
                add_axiom({offset_ge_0, i_eq_m1});
            }
        }
    }

    void theory_str_noodler::tightest_prefix(expr* s, expr* x) {
        expr_ref s1 = mk_first(s);
        expr_ref c  = mk_last(s);
        expr_ref s1c = mk_concat(s1, m_util_s.str.mk_unit(c));
        literal s_eq_emp = mk_eq_empty(s);
        add_axiom({s_eq_emp, mk_eq(s, s1c,true)});
        add_axiom({s_eq_emp, ~mk_literal(m_util_s.str.mk_contains(mk_concat(x, s1), s))});
    }

    expr_ref theory_str_noodler::mk_first(expr* s) {
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_string(str.extract(0, str.length()-1)), m);
        }
        return mk_skolem(symbol("seq_first"), s);
    }

    expr_ref theory_str_noodler::mk_last(expr* s) {
        zstring str;
        if (m_util_s.str.is_string(s, str) && str.length() > 0) {
            return expr_ref(m_util_s.str.mk_char(str, str.length()-1), m);
        }
        sort* char_sort = nullptr;
        VERIFY(m_util_s.is_seq(s->get_sort(), char_sort));
        return mk_skolem(symbol("seq_last"), s, nullptr, nullptr, nullptr, char_sort);
    }

    expr_ref theory_str_noodler::mk_concat(expr* e1, expr* e2) {
        return expr_ref(m_util_s.str.mk_concat(e1, e2), m);
    }

    literal theory_str_noodler::mk_eq_empty(expr* _e, bool phase) {
        context& ctx = get_context();
        expr_ref e(_e, m);
        SASSERT(m_util_s.is_seq(e));
        expr_ref emp(m);
        zstring s;
        if (m_util_s.str.is_empty(e)) {
            return true_literal;
        }
        expr_ref_vector concats(m);
        m_util_s.str.get_concat(e, concats);
        for (auto c : concats) {
            if (m_util_s.str.is_unit(c)) {
                return false_literal;
            }
            if (m_util_s.str.is_string(c, s) && s.length() > 0) {
                return false_literal;
            }
        }
        emp = m_util_s.str.mk_empty(e->get_sort());

        literal lit = mk_eq(e, emp, false);
        ctx.force_phase(phase?lit:~lit);
        ctx.mark_as_relevant(lit);
        return lit;
    }


    // e = prefix(x, y), check if x is a prefix of y
    void theory_str_noodler::handle_prefix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref s = mk_skolem(symbol("m_prefix_right"), x, y);
            expr_ref xs(m_util_s.str.mk_concat(x, s), m);
            string_theory_propagation(xs);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(y, xs, false)});
        }
    }

// e = prefix(x, y), check if x is not a prefix of y
    void theory_str_noodler::handle_not_prefix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref p= mk_skolem(symbol("m_not_prefix_left"), x, y);
            expr_ref mx= mk_skolem(symbol("m_not_prefix_midx"), x, y);
            expr_ref my= mk_skolem(symbol("m_not_prefix_midy"), x, y);
            expr_ref qx= mk_skolem(symbol("m_not_prefix_rightx"), x, y);
            expr_ref qy= mk_skolem(symbol("m_not_prefix_righty"), x, y);

            expr_ref len_x_gt_len_y{m_util_a.mk_gt(m_util_a.mk_sub(m_util_s.str.mk_length(x),m_util_s.str.mk_length(y)), m_util_a.mk_int(0)),m};

            literal len_y_gt_len_x = mk_literal(len_x_gt_len_y);

            expr_ref pmx(m_util_s.str.mk_concat(p, mx), m);
            string_theory_propagation(pmx);
            expr_ref pmxqx(m_util_s.str.mk_concat(pmx, qx), m);
            string_theory_propagation(pmxqx);

            expr_ref pmy(m_util_s.str.mk_concat(p, my), m);
            string_theory_propagation(pmy);
            expr_ref pmyqy(m_util_s.str.mk_concat(pmy, qy), m);
            string_theory_propagation(pmyqy);

            literal x_eq_pmq = mk_eq(x,pmxqx,false);
            literal y_eq_pmq = mk_eq(y,pmyqy,false);

            literal len_mx_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(mx),false);
            literal len_my_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(my),false);
            literal eq_mx_my = mk_eq(mx, my,false);

            literal lit_e = mk_literal(e);
            add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, len_mx_is_one});
            add_axiom({lit_e, len_y_gt_len_x, len_my_is_one});
            add_axiom({lit_e, len_y_gt_len_x, ~eq_mx_my});
        }
    }


    // e = suffix(x, y), check if x is a suffix of y
    void theory_str_noodler::handle_suffix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_suffix(e, x, y));

            expr_ref p = mk_skolem(symbol("m_suffix_left"), x, y);
            expr_ref px(m_util_s.str.mk_concat(p, x), m);
            string_theory_propagation(px);
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(y, px, false)});
        }
    }

    // e = suffix(x, y), check if x is not a suffix of y
    void theory_str_noodler::handle_not_suffix(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);

            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_prefix(e, x, y));

            expr_ref q= mk_skolem(symbol("m_not_suffix_right"), x, y);
            expr_ref mx= mk_skolem(symbol("m_not_suffix_midx"), x, y);
            expr_ref my= mk_skolem(symbol("m_not_suffix_midy"), x, y);
            expr_ref px= mk_skolem(symbol("m_not_suffix_leftx"), x, y);
            expr_ref py= mk_skolem(symbol("m_not_suffix_lefty"), x, y);



            expr_ref len_x_gt_len_y{m_util_a.mk_gt(m_util_a.mk_sub(m_util_s.str.mk_length(x),m_util_s.str.mk_length(y)), m_util_a.mk_int(0)),m};

            literal len_y_gt_len_x = mk_literal(len_x_gt_len_y);

            expr_ref pxmx(m_util_s.str.mk_concat(px, mx), m);
            string_theory_propagation(pxmx);
            expr_ref pxmxq(m_util_s.str.mk_concat(pxmx, q), m);
            string_theory_propagation(pxmxq);

            expr_ref pymy(m_util_s.str.mk_concat(py, my), m);
            string_theory_propagation(pymy);
            expr_ref pymyq(m_util_s.str.mk_concat(pymy, q), m);
            string_theory_propagation(pymyq);

            literal x_eq_pmq = mk_eq(x,pxmxq,false);
            literal y_eq_pmq = mk_eq(y,pymyq,false);

            literal len_mx_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(mx),false);
            literal len_my_is_one = mk_eq(m_util_a.mk_int(1), m_util_s.str.mk_length(my),false);
            literal eq_mx_my = mk_eq(mx, my,false);

            literal lit_e = mk_literal(e);
            add_axiom({lit_e, len_y_gt_len_x, x_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, y_eq_pmq});
            add_axiom({lit_e, len_y_gt_len_x, len_mx_is_one});
            add_axiom({lit_e, len_y_gt_len_x, len_my_is_one});
            add_axiom({lit_e, len_y_gt_len_x, ~eq_mx_my});
        }
    }

    // e = contains(x, y)
    void theory_str_noodler::handle_contains(expr *e) {
        if(!axiomatized_terms.contains(e)||false) {
            axiomatized_terms.insert(e);
            ast_manager &m = get_manager();
            expr *x = nullptr, *y = nullptr;
            VERIFY(m_util_s.str.is_contains(e, x, y));
            expr_ref p = mk_skolem(symbol("m_contains_left"), x, y);
            expr_ref s = mk_skolem(symbol("m_contains_right"), x, y);
            expr_ref pys(m_util_s.str.mk_concat(m_util_s.str.mk_concat(p, y), s), m);

            string_theory_propagation(pys);
//            expr_ref not_e(m.mk_not(e),m);
//            add_axiom(m.mk_or(not_e, m.mk_eq(y, pys)));
            literal not_e = mk_literal(mk_not({e, m}));
            add_axiom({not_e, mk_eq(x, pys, false)});
        }

    }

    void theory_str_noodler::handle_in_re(expr *const e, const bool is_true) {
        expr *s = nullptr, *re = nullptr;
        VERIFY(m_util_s.str.is_in_re(e, s, re));
        ast_manager& m = get_manager();



        STRACE("str", tout  << "handle_in_re " << mk_pp(e, m) << " " << is_true << std::endl;);

    //    expr_ref tmp{e, m};
    //    m_rewrite(tmp);
    //    if ((m.is_false(tmp) && is_true) || (m.is_true(tmp) && !is_true)) {
    //        literal_vector lv;
    //        lv.push_back(is_true ? mk_literal(e) : ~mk_literal(e));
    //        set_conflict(lv);
    //        return;
    //    }
        expr_ref r{re, m};
        this->m_membership_todo.push_back(std::make_tuple(expr_ref(s, m), r, is_true));
    }

    void theory_str_noodler::set_conflict(const literal_vector& lv) {
        context& ctx = get_context();
        const auto& js = ext_theory_conflict_justification{
                get_id(), ctx, lv.size(), lv.data(), 0, nullptr, 0, nullptr};
        ctx.set_conflict(ctx.mk_justification(js));
        STRACE("str", ctx.display_literals_verbose(tout << "[Conflict]\n", lv) << '\n';);
    }

    void theory_str_noodler::block_curr_assignment() {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        bool on_screen=false;
        context& ctx = get_context();

        if(on_screen) std::cout<<"[block] ";
        for (const auto& we : m_word_eq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"="<<we.second<<")";
        }
        for (const auto& we : m_word_diseq_var_todo) {
            if(on_screen) std::cout<<"("<<we.first<<"!="<<we.second<<")";
        }
        if(on_screen) std::cout<<std::endl;

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        STRACE("str", tout << "[Refinement]\nformulas:\n";);
        for (const auto& we : this->m_word_eq_todo_rel) {
            expr *const e = m.mk_not(ctx.mk_eq_atom(we.first, we.second));
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << we.first << " = " << we.second << '\n';);
        }

        literal_vector ls;
        for (const auto& wi : this->m_word_diseq_todo_rel) {
//            expr *const e = mk_eq_atom(wi.first, wi.second);
            expr_ref e(ctx.mk_eq_atom(wi.first, wi.second), m);
            refinement = refinement == nullptr ? e : m.mk_or(refinement, e);
            STRACE("str", tout << wi.first << " != " << wi.second << " " << ctx.get_bool_var(e)<< '\n';);
        }

        for (const auto& in : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(in), std::get<1>(in)), m);
            if(std::get<2>(in)){
                in_app = m.mk_not(in_app);
            }
            refinement = refinement == nullptr ? in_app : m.mk_or(refinement, in_app);
            //STRACE("str", tout << wi.first << " != " << wi.second << '\n';);
        }
        
        if (refinement != nullptr) {
            add_block_axiom(refinement);
        }
        STRACE("str", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);

    }

    void theory_str_noodler::block_len(int n_cnt) {
        STRACE("str", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        context& ctx = get_context();
        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        expr *refinement_len_1 = nullptr;
        expr *refinement_len = nullptr;
        expr *refinement_len_2 = nullptr;
        expr *refinement_len_3 = nullptr;

        STRACE("str", tout << "[Len Refinement]\nformulas:\n";);
        for (const auto& we : this->m_word_eq_todo_rel) {

            vector<expr*> vars;
            this->get_variables(to_app(we.first.get()), vars);
            this->get_variables(to_app(we.second.get()), vars);

            for(expr * const var : vars) {
                std::cout << mk_pp(var, m) << std::endl;
                expr_ref len_str_l(m_util_s.str.mk_length(var), m);
                SASSERT(len_str_l);
                // build RHS
                expr_ref num(m);
                num = m_util_a.mk_numeral(rational(n_cnt), true);
                app *lhs_eq_rhs_1 = m_util_a.mk_le(len_str_l, num);

                refinement_len_1 = refinement_len_1 == nullptr ? lhs_eq_rhs_1 : m.mk_and(refinement_len_1, lhs_eq_rhs_1);

                expr_ref len_str_2(m_util_s.str.mk_length(var), m);
                SASSERT(len_str_2);
                // build RHS
                expr_ref num2(m);
                num2 = m_util_a.mk_numeral(rational(n_cnt+1), true);
                app *lhs_eq_rhs_2 = m_util_a.mk_le(len_str_2, num2);
                refinement_len_2 = refinement_len_2 == nullptr ? lhs_eq_rhs_2 : m.mk_and(refinement_len_2, lhs_eq_rhs_2);

                expr_ref len_str_3(m_util_s.str.mk_length(var), m);
                SASSERT(len_str_3);
                // build RHS
                expr_ref num3(m);
                num3 = m_util_a.mk_numeral(rational(n_cnt+2), true);
                app *lhs_eq_rhs_3 = m_util_a.mk_le(len_str_3, num3);
                refinement_len_3 = refinement_len_3 == nullptr ? lhs_eq_rhs_3 : m.mk_and(refinement_len_3, lhs_eq_rhs_3);
            }

            expr *const e = ctx.mk_eq_atom(we.first, we.second);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        refinement_len = refinement_len_2 == nullptr ? refinement_len_1 : m.mk_or(refinement_len_1, m.mk_or(refinement_len_2, refinement_len_3));
        refinement = m.mk_or(m.mk_not(refinement), refinement_len);
        std::cout << mk_pp(refinement, m) << std::endl;

        add_axiom(refinement);
    }

    void theory_str_noodler::dump_assignments() const {
        STRACE("str", \
                ast_manager& m = get_manager();
                context& ctx = get_context();
                std::cout << "dump all assignments:\n";
                expr_ref_vector assignments{m};


                ctx.get_assignments(assignments);
                for (expr *const e : assignments) {
                   // ctx.mark_as_relevant(e);
                    std::cout <<"**"<< mk_pp(e, m) << (ctx.is_relevant(e) ? "\n" : " (not relevant)\n");
                }
        );
    }

    /**
    Get variable from a given expression @p ex. Append to the output parameter @p res. 
    @param ex Expression to be checked for variables.
    @param[out] res Vector of found variables (may contain duplicities).
    */
    void theory_str_noodler::get_variables(expr* const ex, vector<expr*>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
            res.push_back(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);
        SASSERT(m_util_s.str.is_concat(ex_app));

        SASSERT(ex_app->get_num_args() == 2);
        app *a_x = to_app(ex_app->get_arg(0));
        app *a_y = to_app(ex_app->get_arg(1));
        this->get_variables(a_x, res);
        this->get_variables(a_y, res);
    }

    /**
    Collect basic terms (vars, literals) from a concatenation @p ex. Append the basic terms 
    to the output parameter @p terms. 
    @param ex Expression to be checked for basic terms.
    @param[out] terms Vector of found BasicTerm (in right order).
    */
    void theory_str_noodler::collect_terms(const app* ex, std::vector<BasicTerm>& terms) { 
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
        this->collect_terms(a_x, terms);
        this->collect_terms(a_y, terms);
    }

    /**
    Convert equation/disaequation @p ex to the instance of Predicate.
    @param ex Z3 expression to be converted to Predicate.
    @return Instance of predicate
    */
    Predicate theory_str_noodler::conv_eq_pred(const app* ex) { 
        const app* eq = ex;
        if(m.is_not(ex)) {
            SASSERT(is_app(ex->get_arg(0)));
            SASSERT(ex->get_num_args() == 1);
            eq = to_app(ex->get_arg(0));
        }
        SASSERT(ex->get_num_args() == 2);
        SASSERT(eq->get_arg(0));
        SASSERT(eq->get_arg(1));

        std::vector<BasicTerm> left, right;
        this->collect_terms(to_app(eq->get_arg(0)), left);
        this->collect_terms(to_app(eq->get_arg(1)), right);

        return Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>{left, right}); 
    }

    /**
    Convert conjunction of equations/disequations to the instance of Formula.
    @param conj Conjunction in the form of a set of (dis)equations
    @param[out] res Resulting formula
    */
    void theory_str_noodler::conj_instance(const obj_hashtable<app>& conj, Formula &res) {
        for(app *const pred : conj) {
            Predicate inst = this->conv_eq_pred(pred);
            STRACE("str", tout  << "instance conversion " << inst.to_string() << std::endl;);
            res.add_predicate(inst);
        } 
    }


}
