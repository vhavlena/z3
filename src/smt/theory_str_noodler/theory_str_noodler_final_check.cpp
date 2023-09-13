#include <mata/nfa/builder.hh>
#include "smt/theory_str_noodler/theory_str_noodler.h"

namespace smt::noodler {
    Predicate theory_str_noodler::conv_eq_pred(app* const ex) {
        const app* eq = ex;
        PredicateType ptype = PredicateType::Equation;
        if(m.is_not(ex)) {
            SASSERT(is_app(ex->get_arg(0)));
            SASSERT(ex->get_num_args() == 1);
            eq = to_app(ex->get_arg(0));
            ptype = PredicateType::Inequation;
        }
        SASSERT(eq->get_num_args() == 2);
        SASSERT(eq->get_arg(0));
        SASSERT(eq->get_arg(1));

        obj_hashtable<expr> vars;
        util::get_str_variables(ex, this->m_util_s, this->m, vars);
        for(expr * const v : vars) {

            BasicTerm vterm(BasicTermType::Variable, to_app(v)->get_name().str());
            this->var_name.insert({vterm, expr_ref(v, this->m)});
        }

        std::vector<BasicTerm> left, right;
        util::collect_terms(to_app(eq->get_arg(0)), m, this->m_util_s, this->predicate_replace, this->var_name, left);
        util::collect_terms(to_app(eq->get_arg(1)), m, this->m_util_s, this->predicate_replace, this->var_name, right);

        return Predicate(ptype, std::vector<std::vector<BasicTerm>>{left, right});
    }

    Formula theory_str_noodler::get_word_formula_from_relevant() {
        Formula instance;

        for (const auto &we: this->m_word_eq_todo_rel) {
            Predicate inst = this->conv_eq_pred(ctx.mk_eq_atom(we.first, we.second));
            instance.add_predicate(inst);
        }

        for (const auto& wd : this->m_word_diseq_todo_rel) {
            Predicate inst = this->conv_eq_pred(m.mk_not(ctx.mk_eq_atom(wd.first, wd.second)));
            instance.add_predicate(inst);
        }

        // construct not contains predicates
        for(const auto& not_contains : this->m_not_contains_todo_rel) {
            std::vector<BasicTerm> left, right;
            util::collect_terms(to_app(not_contains.first), m, this->m_util_s, this->predicate_replace, this->var_name, left);
            util::collect_terms(to_app(not_contains.second), m, this->m_util_s, this->predicate_replace, this->var_name, right);
            Predicate inst(PredicateType::NotContains, std::vector<Concat>{left, right});
            instance.add_predicate(inst);
        }

        return instance;
    }

    std::set<Mata::Symbol> theory_str_noodler::get_symbols_from_relevant() {
        std::set<Mata::Symbol> symbols_in_formula{};

        for (const auto &word_equation: m_word_eq_todo_rel) {
            extract_symbols(word_equation.first, symbols_in_formula);
            extract_symbols(word_equation.second, symbols_in_formula);
        }

        for (const auto &word_disequation: m_word_diseq_todo_rel) {
            extract_symbols(word_disequation.first, symbols_in_formula);
            extract_symbols(word_disequation.second, symbols_in_formula);
        }

        for (const auto &membership: m_membership_todo_rel) {
            extract_symbols(std::get<1>(membership), symbols_in_formula);
        }
        // extract from not contains
        for(const auto& not_contains : m_not_contains_todo_rel) {
            extract_symbols(not_contains.first, symbols_in_formula);
            extract_symbols(not_contains.second, symbols_in_formula);
        }

        /* Get number of dummy symbols needed for disequations and 'x not in RE' predicates.
         * We need some dummy symbols, to represent the symbols not occuring in predicates,
         * otherwise, we might return unsat even though the formula is sat. For example if
         * we had x != y and no other predicate, we would have no symbols and the formula
         * would be unsat. With one dummy symbol, it becomes sat.
         * We add new dummy symbols for each diseqation and 'x not in RE' predicate, as we
         * could be in situation where we have for example x != y, y != z, z != x, and
         * |x| = |y| = |z|. If we added only one dummy symbol, then this would be unsat,
         * but if we have three symbols, it becomes sat (which this formula is). We add
         * dummy symbols also for 'x not in RE' because they basically represent
         * disequations too (for example 'x not in "aaa"' and |x| = 3 should be sat, but
         * with only symbol "a" it becomes unsat).
         * 
         * FIXME: We can possibly create more dummy symbols than the size of alphabet
         * (from the string theory standard the size of the alphabet is 196607), but
         * it is an edge-case that probably cannot happen.
         */
        size_t number_of_dummy_symbs = this->m_word_diseq_todo_rel.size();
        for (const auto& membership : this->m_membership_todo_rel) {
            if(!std::get<2>(membership)){
                number_of_dummy_symbs++;
            }
        }
        // to be safe, we set the minimum number of dummy symbols as 3
        number_of_dummy_symbs = std::max(number_of_dummy_symbs, size_t(3));

        // add needed number of dummy symbols to symbols_in_formula
        util::get_dummy_symbols(number_of_dummy_symbs, symbols_in_formula);

        return symbols_in_formula;
    }

    AutAssignment theory_str_noodler::create_aut_assignment_for_formula(
            const Formula& instance,
            const std::set<Mata::Symbol>& noodler_alphabet
    ) {
        AutAssignment aut_assignment{};
        aut_assignment.set_alphabet(noodler_alphabet);
        for (const auto &word_equation: m_membership_todo_rel) {
            const expr_ref& var_expr{ std::get<0>(word_equation) };
            assert(is_app(var_expr));
            const auto& var_app{ to_app(var_expr) };
            assert(var_app->get_num_args() == 0);
            const std::string& variable_name{ var_app->get_decl()->get_name().str() };

            zstring s;
            BasicTerm term{ BasicTermType::Variable, variable_name };
            if(m_util_s.str.is_string(var_app, s)) {
                term = BasicTerm(BasicTermType::Literal, s.encode());
            }
            // If the regular constraint is in a negative form, create a complement of the regular expression instead.
            const bool make_complement{ !std::get<2>(word_equation) };
            Nfa nfa{ regex::conv_to_nfa(to_app(std::get<1>(word_equation)), m_util_s, m, noodler_alphabet, make_complement, make_complement) };
            auto aut_ass_it{ aut_assignment.find(term) };
            if (aut_ass_it != aut_assignment.end()) {
                // This variable already has some regular constraints. Hence, we create an intersection of the new one
                //  with the previously existing.
                aut_ass_it->second = std::make_shared<Nfa>(
                        Mata::Nfa::reduce(Mata::Nfa::intersection(nfa, *aut_ass_it->second)));

            } else { // We create a regular constraint for the current variable for the first time.
                aut_assignment[term] = std::make_shared<Nfa>(std::forward<Nfa>(std::move(nfa)));
                // TODO explain after this function is moved to theory_str_noodler, we do this because var_name contains only variables occuring in instance and not those that occur only in str.in_re
                this->var_name.insert({term, var_expr});
            }
        }

        // create sigma star automaton for our alphabet
        Mata::EnumAlphabet mata_alphabet(noodler_alphabet.begin(), noodler_alphabet.end());
        auto nfa_sigma_star = std::make_shared<Nfa>(Mata::Nfa::Builder::create_sigma_star_nfa(&mata_alphabet));
        // remove the pointer to alphabet in the automaton, as it points to local variable (and we have the alphabet in aut_assignment)
        nfa_sigma_star->alphabet = nullptr;

        // some variables/literals are not assigned to anything yet, we need to fix that
        for (const auto &pred : instance.get_predicates()) {
            for (const auto &side : pred.get_params()) {
                for (const auto &var_or_literal : side) {
                    if (var_or_literal.is_variable() && aut_assignment.find(var_or_literal) == aut_assignment.end()) {
                        // assign sigma star automaton for all yet unassigned variables
                        aut_assignment[var_or_literal] = nfa_sigma_star;
                    } else if (var_or_literal.is_literal()) {
                        // to string literals. assign automaton accepting the word denoted by the literal
                        // TODO if Z3 can give us `string literal in RE` then we should check if aut_assignment does not contain this literal already (if yes, do intersection)
                        Nfa nfa{ AutAssignment::create_word_nfa(var_or_literal.get_name()) };
                        aut_assignment.emplace(var_or_literal, std::make_shared<Nfa>(std::move(nfa)));
                    }
                }
            }
        }

        TRACE("str-nfa",
            tout << "Created automata assignment for formula:" << std::endl;
            for (const auto& single_aut_assignment: aut_assignment) {
               tout << "Automaton for " << single_aut_assignment.first.get_name() << ":" << std::endl;
               single_aut_assignment.second->print_to_DOT(tout);
            }
        );

        return aut_assignment;
    }

    std::unordered_set<BasicTerm> theory_str_noodler::get_init_length_vars(AutAssignment& ass) {
        std::unordered_set<BasicTerm> init_lengths{};
        for (const auto& len : len_vars) {
            BasicTerm v = util::get_variable_basic_term(len);
            if(ass.find(v) != ass.end())
                init_lengths.emplace(v);
        }
        return init_lengths;
    }

    bool theory_str_noodler::solve_lang_eqs_diseqs() {
        for(const auto& item : this->m_lang_eq_or_diseq_todo_rel) {
            // RegLan variables should not occur here, they are eliminated by z3 rewriter I think,
            // so both sides of the (dis)equations should be terms representing reg. languages
            expr_ref left_side = std::get<0>(item);
            expr_ref right_side = std::get<1>(item);
            bool is_equation = std::get<2>(item);

            STRACE("str",
                tout << "Checking lang (dis)eq: " << mk_pp(left_side, m) << (is_equation ? " == " : " != ") << mk_pp(right_side, m) << std::endl;
            );

            // get symbols from both sides
            std::set<uint32_t> alphabet;
            extract_symbols(left_side, alphabet);
            extract_symbols(right_side, alphabet);

            // construct NFAs for both sides
            Mata::Nfa::Nfa nfa1 = regex::conv_to_nfa(to_app(left_side), m_util_s, m, alphabet, false );
            Mata::Nfa::Nfa nfa2 = regex::conv_to_nfa(to_app(right_side), m_util_s, m, alphabet, false );

            // check if NFAs are equivalent (if we have equation) or not (if we have disequation)
            bool are_equiv = Mata::Nfa::are_equivalent(nfa1, nfa2);
            if ((is_equation && !are_equiv) || (!is_equation && are_equiv)) {
                // the language (dis)equation does not hold => block it and return
                app_ref lang_eq(m.mk_eq(left_side, right_side), m);
                if(is_equation){
                    STRACE("str", tout << mk_pp(lang_eq, m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(m.mk_not(lang_eq))});
                } else {
                    STRACE("str", tout << mk_pp(m.mk_not(lang_eq), m) << " is unsat" << std::endl);
                    add_axiom({mk_literal(lang_eq)});
                }
                return false;
            }
        }

        // if we are here, all (dis)equations hold
        return true;
    }

    lbool theory_str_noodler::solve_underapprox(const Formula& instance, const AutAssignment& aut_assignment, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        DecisionProcedure dec_proc = DecisionProcedure{ instance, aut_assignment, init_length_sensitive_vars, m_params };
        if (dec_proc.preprocess(PreprocessType::UNDERAPPROX) == l_false) {
            return l_false;
        }

        dec_proc.init_computation();
        while(dec_proc.compute_next_solution() == l_true) {
            expr_ref lengths = len_node_to_z3_formula(dec_proc.get_lengths());
            if(check_len_sat(lengths) == l_true) {
                return l_true;
            }
        }
        return l_false;
    }

    lbool theory_str_noodler::check_len_sat(expr_ref len_formula, expr_ref* unsat_core) {
        if (len_formula == m.mk_true()) {
            // we assume here that existing length constraints are satisfiable, so adding true will do nothing
            return l_true;
        }

        int_expr_solver m_int_solver(get_manager(), get_context().get_fparams());
        // do we solve only regular constraints? If yes, skip other temporary length constraints (they are not necessary)
        bool include_ass = true;
        if(this->m_word_diseq_todo_rel.size() == 0 && this->m_word_eq_todo_rel.size() == 0) {
            include_ass = false;
        }
        m_int_solver.initialize(get_context(), include_ass);
        auto ret = m_int_solver.check_sat(len_formula);
        // construct an unsat core --> might be expensive
        // TODO: better interface of m_int_solver
        if(unsat_core != nullptr) {
            for(unsigned i=0;i<m_int_solver.m_kernel.get_unsat_core_size();i++){
                *unsat_core = m.mk_and(*unsat_core, m_int_solver.m_kernel.get_unsat_core_expr(i));
            }
        }
        return ret;
    }

    void theory_str_noodler::block_curr_len(expr_ref len_formula, bool add_axiomatized, bool init_lengths) {
        STRACE("str-block", tout << __LINE__ << " enter " << __FUNCTION__ << std::endl;);

        context& ctx = get_context();

        ast_manager& m = get_manager();
        expr *refinement = nullptr;
        for (const auto& we : this->m_word_eq_todo_rel) {
            // we create the equation according to we
            //expr *const e = m.mk_not(m.mk_eq(we.first, we.second));
            expr *const e = ctx.mk_eq_atom(we.first, we.second);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        literal_vector ls;
        for (const auto& wi : this->m_word_diseq_todo_rel) {
            expr_ref e(m.mk_not(ctx.mk_eq_atom(wi.first, wi.second)), m);
            refinement = refinement == nullptr ? e : m.mk_and(refinement, e);
        }

        for (const auto& in : this->m_membership_todo_rel) {
            app_ref in_app(m_util_s.re.mk_in_re(std::get<0>(in), std::get<1>(in)), m);
            if(!std::get<2>(in)){
                in_app = m.mk_not(in_app);
            }
            if(!ctx.e_internalized(in_app)) {
                ctx.internalize(in_app, false);
            }
            refinement = refinement == nullptr ? in_app : m.mk_and(refinement, in_app);
        }
        
        if(m_params.m_loop_protect && add_axiomatized) {
            this->axiomatized_instances.push_back({expr_ref(refinement, this->m), stored_instance{ .lengths = len_formula, .initial_length = init_lengths}});
        }
        if (refinement != nullptr) {
            add_axiom(m.mk_or(m.mk_not(refinement), len_formula));
        }
        STRACE("str-block", tout << __LINE__ << " leave " << __FUNCTION__ << std::endl;);
    }

    void theory_str_noodler::extract_symbols(expr* const ex, std::set<uint32_t>& alphabet) {
        if (m_util_s.str.is_string(ex)) {
            auto ex_app{ to_app(ex) };
            SASSERT(ex_app->get_num_parameters() == 1);
            const zstring string_literal{ zstring{ ex_app->get_parameter(0).get_zstring() } };
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                alphabet.insert(string_literal[i]);
            }
            return;
        }

        if(util::is_variable(ex, m_util_s)) { // Skip variables.
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        if (m_util_s.re.is_to_re(ex_app)) { // Handle conversion to regex function call.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                util::throw_error("we support only string literals in str.to_re");
            }
            extract_symbols(to_app(arg), alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app) // Handle regex concatenation.
                || m_util_s.str.is_concat(ex_app) // Handle string concatenation.
                || m_util_s.re.is_intersection(ex_app) // Handle intersection.
            ) {
            for (unsigned int i = 0; i < ex_app->get_num_args(); ++i) {
                extract_symbols(to_app(ex_app->get_arg(i)), alphabet);
            }
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            util::throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), alphabet);
            return;
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            util::throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            util::throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus.
            // Handle repeated full char ('.+') (SMT2: (re.+ re.allchar)).
            return;
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty language.
            return;
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon.
            return;
        } else if (m_util_s.re.is_full_char(ex_app)) {
            // Handle full char (single occurrence of any string symbol, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_full_seq(ex_app)) {
            // Handle full sequence of characters (any sequence of characters, '.*') (SMT2: re.all).
            return;
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate.
            util::throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(ex_app) // Handle optional.
                || m_util_s.re.is_plus(ex_app) // Handle positive iteration.
                || m_util_s.re.is_star(ex_app) // Handle star iteration.
                || m_util_s.re.is_loop(ex_app) // Handle loop.
            ) {
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range.
            SASSERT(ex_app->get_num_args() == 2);
            const auto range_begin{ ex_app->get_arg(0) };
            const auto range_end{ ex_app->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            auto current_value{ range_begin_value };
            while (current_value <= range_end_value) {
                alphabet.insert(current_value);
                ++current_value;
            }
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse.
            util::throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), alphabet);
            extract_symbols(to_app(right), alphabet);
            return;
        } else if(util::is_variable(ex_app, m_util_s)) { // Handle variable.
            util::throw_error("variable should not occur here");
        } else {
            // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
            // TODO: maybe we can just leave is_range, is_variable and is_string in this function and otherwise do this:
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                SASSERT(is_app(ex_app->get_arg(i)));
                app *arg = to_app(ex_app->get_arg(i));
                extract_symbols(arg, alphabet);
            }
        }
    }
}
