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

#include "smt/params/smt_params.h"
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_noodler_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include "formula.h"
#include "inclusion_graph.h"
#include "decision_procedure.h"
#include "expr_solver.h"
#include "util.h"
#include "var_union_find.h"
#include "nielsen_decision_procedure.h"

namespace smt::noodler {

    // FIXME add high level explanation of how this works (length vars are got from init_search_eh, predicates are translated in relevant_eh, final_check_eh does this and that etc)
    // FIXME a lot of stuff in this class comes from trau/z3str3 we still need to finish cleaning
    class theory_str_noodler : public theory {
    protected:

        /**
         * Structure for storing items for the loop protection.
         */
        struct stored_instance {
            expr_ref lengths; // length formula 
            bool initial_length; // was the length formula obtained from the initial length checking?
        };

        int m_scope_level = 0;
        const theory_str_noodler_params& m_params;
        th_rewriter m_rewrite;
        arith_util m_util_a;
        seq_util m_util_s;

        // equivalence of z3 terms based on their length (terms are equiv if their length is for sure the same)
        var_union_find var_eqs;

        // variables whose lengths are important
        obj_hashtable<expr> len_vars;

        // used in final_check_eh, maps noodler variables to z3 string variables
        std::map<BasicTerm, expr_ref> var_name;

        // mapping predicates and function to variables that they substitute to
        obj_map<expr, expr*> predicate_replace;

        // TODO what are these?
        std::vector<app_ref> axiomatized_len_axioms;
        obj_hashtable<expr> axiomatized_terms;
        obj_hashtable<expr> axiomatized_persist_terms;
        obj_hashtable<expr> propgated_string_theory;
        obj_hashtable<expr> m_has_length;          // is length applied
        expr_ref_vector     m_length;             // length applications themselves
        std::vector<std::pair<expr_ref, stored_instance>> axiomatized_instances;

        // TODO what are these?
        vector<std::pair<obj_hashtable<expr>,std::vector<app_ref>>> len_state;
        obj_map<expr, unsigned> bool_var_int;
        obj_hashtable<expr> bool_var_state;

        using expr_pair = std::pair<expr_ref, expr_ref>;
        using expr_pair_flag = std::tuple<expr_ref, expr_ref, bool>;

        // constraints that are (possibly) to be processed in final_check_eh (added either in relevant_eh or ?assign_eh?)
        // they also need to be popped and pushed in pop_scope_eh and push_scope_eh)
        scoped_vector<expr_pair> m_word_eq_todo; // pair contains left and right side of the (word) equality
        scoped_vector<expr_pair> m_word_diseq_todo; // pair contains left and right side of the (word) disequality
        scoped_vector<expr_pair> m_lang_eq_todo; //pair contains left and right side of the language equality
        scoped_vector<expr_pair> m_lang_diseq_todo; // pair contains left and right side of the language disequality
        scoped_vector<expr_pair> m_not_contains_todo; // first element should not contain the second one
        scoped_vector<expr_pair_flag> m_membership_todo; // contains the variable and reg. lang. + flag telling us if it is negated (false -> negated)

        // during final_check_eh, we call remove_irrelevant_constr which chooses from previous sets of
        // todo constraints and check if they are relevant for current SAT assignment => if they are
        // they are added to one of these sets
        vector<expr_pair> m_word_eq_todo_rel; // pair contains left and right side of the equality
        vector<expr_pair> m_word_diseq_todo_rel; // pair contains left and right side of the disequality
        vector<expr_pair_flag> m_lang_eq_or_diseq_todo_rel; // contains and right side of the (dis)equality and a flag - true -> equality, false -> diseq
        vector<expr_pair_flag> m_membership_todo_rel; // contains the variable and reg. lang. + flag telling us if it is negated (false -> negated)
        vector<expr_pair> m_not_contains_todo_rel; // not contains

    public:
        char const * get_name() const override { return "noodler"; }
        theory_str_noodler(context& ctx, ast_manager & m, theory_str_noodler_params const & params);
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

        // FIXME ensure_enode is non-virtual function of theory, why are we redegfining it?
        enode* ensure_enode(expr* e);

        void add_length_axiom(expr* n);

        /**
         * @brief Get concatenation of e1 and e2
         */
        expr_ref mk_concat(expr* e1, expr* e2);

        /**
         * @brief Creates literal representing that n is empty string
         */
        literal mk_eq_empty(expr* n);

        bool has_length(expr *e) const { return m_has_length.contains(e); }
        void enforce_length(expr* n);

        ~theory_str_noodler() {}

    protected:
        expr_ref mk_sub(expr *a, expr *b);

        literal mk_literal(expr *e);
        bool_var mk_bool_var(expr *e);
        /**
         * @brief Create a fresh Z3 string variable with a given @p name followed by a unique suffix.
         *
         * @param name Infix of the name (rest is added to get a unique name)
         * FIXME same function is in theory_str_noodler, decide which to keep
         */
        expr_ref mk_str_var_fresh(const std::string& name);
        /**
         * @brief Create a fresh Z3 int variable with a given @p name followed by a unique suffix.
         *
         * @param name Infix of the name (rest is added to get a unique name)
         * FIXME same function is in theory_str_noodler, decide which to keep
         */
        expr_ref mk_int_var_fresh(const std::string& name);

        /**
         * @brief Transforms LenNode to the z3 formula
         * 
         * Uses mapping var_name, those variables v that are mapped are assumed to be string variables
         * and will be transformed into (str.len v) while other variables (which are probably created
         * during preprocessing/decision procedure) are taken as int variables.
         */
        expr_ref len_node_to_z3_formula(const LenNode& len_formula);

        /**
         * @brief Adds @p e as a theory axiom (i.e. to SAT solver).
         * 
         * @param e Axiom to add, probably should be a predicate.
         * 
         * TODO Nobody probably knows what happens in here.
         */
        void add_axiom(expr *e);
        /**
         * @brief Adds a new clause of literals from @p ls.
         * 
         * TODO Nobody probably knows what happens in here, and it is a bit different than the other add_axiom
         */
        void add_axiom(std::vector<literal> ls);

        // methods for rewriting different predicates into something simpler that we can handle
        void handle_char_at(expr *e);
        void handle_substr(expr *e);
        void handle_substr_int(expr *e);
        void handle_index_of(expr *e);
        void handle_replace(expr *e);
        void handle_prefix(expr *e);
        void handle_suffix(expr *e);
        void handle_not_prefix(expr *e);
        void handle_not_suffix(expr *e);
        void handle_contains(expr *e);
        void handle_not_contains(expr *e);
        void handle_in_re(expr *e, bool is_true);

        // methods for assigning boolean values to predicates
        void assign_not_contains(expr *e);

        void set_conflict(const literal_vector& ls);

        expr_ref construct_refinement();
        void string_theory_propagation(expr * ex, bool init = false, bool neg = false);
        void propagate_concat_axiom(enode * cat);
        void propagate_basic_string_axioms(enode * str);

        /**
         * Creates theory axioms that hold iff either any of the negated assumption from @p neg_assumptions holds,
         * or string term @p s does not occur in @p x@p s other than at the end. I.e. we are checking
         * (not-negated assumptions) -> (string term @p s does not occur in @p x@p s other than at the end)
         * 
         * It does it by checking that s does not occur anywhere in xs reduced by one character (i.e. xs[0:-2])
         * 
         * Translates to the following theory axioms:
         * not(s = eps) -> neg_assumptions || s = s1.s2
         * not(s = eps) -> neg_assumptions || s2 in re.allchar (is a single character)
         * not(s = eps) -> neg_assumptions || not(contains(x.s1, s))
         * (s = eps) && (x != eps) -> neg_assumptions
         * 
         * For the case that s is a string literal, we do not add the two first axioms and we take s1 = s[0:-2].
         * 
         * @param neg_assumptions Negated assumptions that have to hold for checking tightest prefix
         */
        void tightest_prefix(expr* s, expr* x, std::vector<literal> neg_assumptions);

        /******************* FINAL_CHECK_EH HELPING FUNCTIONS *********************/

        /**
         * @brief Adds string constraints from *_todo that are relevant for SAT checking to *_todo_rel.
         */
        void remove_irrelevant_constr();

        /**
        Convert (dis)equation @p ex to the instance of Predicate. As a side effect updates mapping of
        variables (BasicTerm) to the corresponding z3 expr.
        @param ex Z3 expression to be converted to Predicate.
        @return Instance of predicate
        */
        Predicate conv_eq_pred(app* expr);
        /**
         * @brief Creates noodler formula containing relevant word equations and disequations
         */
        Formula get_word_formula_from_relevant();
        /**
         * @brief Get all symbols used in relevant word (dis)equations and memberships
         */
        std::set<Mata::Symbol> get_symbols_from_relevant();
        /**
         * Get automata assignment for formula @p instance using relevant memberships in m_membership_todo_rel.
         * As a side effect updates mapping of variables (BasicTerm) to the corresponding z3 expr.
         * @param instance Formula containing (dis)equations
         * @param noodler_alphabet Set of symbols occuring in the formula and memberships
         */
        [[nodiscard]] AutAssignment create_aut_assignment_for_formula(
                const Formula& instance,
                const std::set<Mata::Symbol>& noodler_alphabet
        );
        /**
         * Get initial length variables as a set of @c BasicTerm from their expressions.
         */
        std::unordered_set<BasicTerm> get_init_length_vars(AutAssignment& ass);

        /**
         * Solves relevant language (dis)equations from m_lang_eq_or_diseq_todo_rel. If some of them
         * does not hold, returns false and also blocks it in the SAT assignment.
         */
        bool solve_lang_eqs_diseqs();
        /**
         * Solve the problem using underapproximating decision procedure, if it returns l_true,
         * the original formula is SAT, otherwise we need to run normal decision procedure.
         */
        lbool solve_underapprox(const Formula& instance, const AutAssignment& aut_ass, const std::unordered_set<BasicTerm>& init_length_sensitive_vars);

        /**
         * @brief Check if the length formula @p len_formula is satisfiable with the existing length constraints.
         * 
         * @param[out] unsat_core If this parameter is NOT nullptr, the LIA solver stores here unsat core of 
         * the current @p len_formula. If the parameter is nullptr, the unsat core is not computed.
         */
        lbool check_len_sat(expr_ref len_formula, expr_ref* unsat_core=nullptr);

        /**
         * @brief Blocks current SAT assignment for given @p len_formula
         * 
         * @param len_formula Length formula corresponding to the current instance
         * @param add_axiomatized Add item to the vector of axiomatized instances (for the loop protection)
         * @param init_lengths Was the length formula obtained from the initial length checking (for the fool protection)
         * 
         * TODO explain better
         */
        void block_curr_len(expr_ref len_formula, bool add_axiomatized = true, bool init_lengths = false);

        /***************** FINAL_CHECK_EH HELPING FUNCTIONS END *******************/
    };
}

#endif /* _THEORY_STR_NOODLER_H_ */
