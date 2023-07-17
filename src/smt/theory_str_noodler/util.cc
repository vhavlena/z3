#include <cassert>
#include <mata/re2parser.hh>

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "util/z3_exception.h"

namespace {
    using Mata::Nfa::Nfa;
}

namespace smt::noodler::util {

    void throw_error(std::string errMsg) {
        // TODO maybe for benchnarking throw_error in release should also really throw error
#ifndef NDEBUG
        // for debugging, we use std::runtime_error, because that one is not caught by z3
        throw std::runtime_error(errMsg);
#else
        // for release, we use this, as it is caught by z3 and it transform it into 'unknown'
        throw default_exception(std::move(errMsg));
#endif
    }

    void extract_symbols(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet) {
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
                throw_error("we support only string literals in str.to_re");
            }
            extract_symbols(to_app(arg), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app) // Handle regex concatenation.
                || m_util_s.str.is_concat(ex_app) // Handle string concatenation.
                || m_util_s.re.is_intersection(ex_app) // Handle intersection.
            ) {
            for (unsigned int i = 0; i < ex_app->get_num_args(); ++i) {
                extract_symbols(to_app(ex_app->get_arg(i)), m_util_s, m, alphabet);
            }
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            throw_error("regex difference is unsupported");
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
            throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(ex_app) // Handle optional.
                || m_util_s.re.is_plus(ex_app) // Handle positive iteration.
                || m_util_s.re.is_star(ex_app) // Handle star iteration.
                || m_util_s.re.is_loop(ex_app) // Handle loop.
            ) {
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
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
            throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if(is_variable(ex_app, m_util_s)) { // Handle variable.
            throw_error("variable should not occur here");
        } else {
            // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
            // TODO: maybe we can just leave is_range, is_variable and is_string in this function and otherwise do this:
            for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
                SASSERT(is_app(ex_app->get_arg(i)));
                app *arg = to_app(ex_app->get_arg(i));
                extract_symbols(arg, m_util_s, m, alphabet);
            }
        }
    }

    void get_str_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res, obj_map<expr, expr*>* pred_map) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_str_variable(ex, m_util_s)) {
            res.insert(ex);
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };
        if(pred_map != nullptr) {
            expr* rpl;
            if(pred_map->find(ex_app, rpl)) {
                get_str_variables(rpl, m_util_s, m, res, pred_map);
            }
        }

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_str_variables(arg, m_util_s, m, res, pred_map);
        }
    }

    void get_variable_names(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_variable(ex, m_util_s)) {
            res.insert(std::to_string(to_app(ex)->get_name()));
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app{ to_app(ex) };

        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_variable_names(arg, m_util_s, m, res);
        }
    }

    bool is_variable(const expr* expression, const seq_util& m_util_s) {
        // TODO: When we are able to detect other kinds of variables, add their checks here.
        return is_str_variable(expression, m_util_s);
    }

    bool is_str_variable(const expr* expression, const seq_util& m_util_s) {
        if(m_util_s.str.is_string(expression)) { // Filter away string literals first.
            return false;
        }

        // TODO: we are not sure if this is correct, we just hope
        if (m_util_s.is_string(expression->get_sort()) &&
            is_app(expression) && to_app(expression)->get_num_args() == 0) {
            return true;
        }

        return false;
    }

    std::set<uint32_t> get_dummy_symbols(size_t new_symb_num, std::set<uint32_t>& symbols_to_append_to) {
        std::set<uint32_t> dummy_symbols{};
        uint32_t dummy_symbol{ 0 };
        const size_t disequations_number{ new_symb_num };
        for (size_t diseq_index{ 0 }; diseq_index < disequations_number; ++diseq_index) {
            while (symbols_to_append_to.find(dummy_symbol) != symbols_to_append_to.end()) { ++dummy_symbol; }
            dummy_symbols.insert(dummy_symbol);
            ++dummy_symbol;
        }
        [[maybe_unused]] const size_t dummy_symbols_number{ dummy_symbols.size() };
        assert(dummy_symbols_number == disequations_number);
        [[maybe_unused]] const size_t symbols_in_formula_number{ symbols_to_append_to.size() };
        symbols_to_append_to.insert(dummy_symbols.begin(), dummy_symbols.end());
        assert(dummy_symbols_number + symbols_in_formula_number == symbols_to_append_to.size());
        return dummy_symbols;
    }

    [[nodiscard]] Nfa conv_to_nfa(const app *expression, const seq_util& m_util_s, const ast_manager& m,
                                  const std::set<uint32_t>& alphabet, bool determinize, bool make_complement) {
        Nfa nfa{};

        if (m_util_s.re.is_to_re(expression)) { // Handle conversion of to regex function call.
            SASSERT(expression->get_num_args() == 1);
            const auto arg{ expression->get_arg(0) };
            // Assume that expression inside re.to_re() function is a string of characters.
            if (!m_util_s.str.is_string(arg)) { // if to_re has something other than string literal
                throw_error("we support only string literals in str.to_re");
            }
            nfa = conv_to_nfa(to_app(arg), m_util_s, m, alphabet, determinize);
        } else if (m_util_s.re.is_concat(expression)) { // Handle regex concatenation.
            SASSERT(expression->get_num_args() > 0);
            nfa = conv_to_nfa(to_app(expression->get_arg(0)), m_util_s, m, alphabet);
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                nfa.concatenate(conv_to_nfa(to_app(expression->get_arg(i)), m_util_s, m, alphabet, determinize));
            }
        } else if (m_util_s.re.is_antimirov_union(expression)) { // Handle Antimirov union.
            throw_error("antimirov union is unsupported");
        } else if (m_util_s.re.is_complement(expression)) { // Handle complement.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet, determinize);
            // According to make_complement, we do complement at the end, so we just invert it
            make_complement = !make_complement;
        } else if (m_util_s.re.is_derivative(expression)) { // Handle derivative.
            throw_error("derivative is unsupported");
        } else if (m_util_s.re.is_diff(expression)) { // Handle diff.
            throw_error("regex difference is unsupported");
        } else if (m_util_s.re.is_dot_plus(expression)) { // Handle dot plus.
            nfa.initial.insert(0);
            nfa.final.insert(1);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 1);
                nfa.delta.add(1, symbol, 1);
            }
        } else if (m_util_s.re.is_empty(expression)) { // Handle empty language.
            // Do nothing, as nfa is initialized empty
        } else if (m_util_s.re.is_epsilon(expression)) { // Handle epsilon.
            nfa = Mata::Nfa::create_empty_string_nfa();
        } else if (m_util_s.re.is_full_char(expression)) { // Handle full char (single occurrence of any string symbol, '.').
            nfa.initial.insert(0);
            nfa.final.insert(1);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 1);
            }
        } else if (m_util_s.re.is_full_seq(expression)) {
            nfa.initial.insert(0);
            nfa.final.insert(0);
            for (const auto& symbol : alphabet) {
                nfa.delta.add(0, symbol, 0);
            }
        } else if (m_util_s.re.is_intersection(expression)) { // Handle intersection.
            SASSERT(expression->get_num_args() > 0);
            nfa = conv_to_nfa(to_app(expression->get_arg(0)), m_util_s, m, alphabet, determinize);
            for (unsigned int i = 1; i < expression->get_num_args(); ++i) {
                nfa = Mata::Nfa::intersection(nfa, conv_to_nfa(to_app(expression->get_arg(i)), m_util_s, m, alphabet, determinize));
            }
        } else if (m_util_s.re.is_loop(expression)) { // Handle loop.
            unsigned low, high;
            expr *body;
            bool is_high_set = false;
            if (m_util_s.re.is_loop(expression, body, low, high)) {
                is_high_set = true;
            } else if (m_util_s.re.is_loop(expression, body, low)) {
                is_high_set = false;
            } else {
                throw_error("loop should contain at least lower bound");
            }

            Nfa body_nfa = conv_to_nfa(to_app(body), m_util_s, m, alphabet, determinize);

            if (Mata::Nfa::is_lang_empty(body_nfa)) {
                // for the case that body of the loop represents empty language...
                if (low == 0) {
                    // ...we either return empty string if we have \emptyset{0,h}
                    nfa = Mata::Nfa::create_empty_string_nfa();
                } else {
                    // ... or empty language
                    nfa = std::move(body_nfa);
                }
            } else {
                body_nfa.unify_final();
                body_nfa.unify_initial();

                body_nfa = Mata::Nfa::reduce(body_nfa);
                nfa = Mata::Nfa::create_empty_string_nfa();
                // we need to repeat body_nfa at least low times
                for (unsigned i = 0; i < low; ++i) {
                    nfa.concatenate(body_nfa);
                }

                // we will now either repeat body_nfa high-low times (if is_high_set) or
                // unlimited times (if it is not set), but we have to accept after each loop,
                // so we add an empty word into body_nfa
                State new_state = nfa.add_state();
                body_nfa.initial.insert(new_state);
                body_nfa.final.insert(new_state);

                body_nfa.unify_initial();
                Mata::Nfa::reduce(body_nfa);

                if (is_high_set) {
                    // if high is set, we repeat body_nfa another high-low times
                    for (unsigned i = 0; i < high - low; ++i) {
                        nfa.concatenate(body_nfa);
                    }
                } else {
                    // if high is not set, we can repeat body_nfa unlimited more times
                    // so we do star operation on body_nfa and add it to end of nfa
                    for (const auto& final : body_nfa.final) {
                        for (const auto& initial : body_nfa.initial) {
                            body_nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                        }
                    }
                    nfa.concatenate(body_nfa);
                    nfa = Mata::Nfa::remove_epsilon(nfa);
                }
            }

        } else if (m_util_s.re.is_of_pred(expression)) { // Handle of predicate.
            throw_error("of predicate is unsupported");
        } else if (m_util_s.re.is_opt(expression)) { // Handle optional.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet, determinize);
            nfa.unify_initial();
            for (const auto& initial : nfa.initial) {
                nfa.final.insert(initial);
            }
        } else if (m_util_s.re.is_range(expression)) { // Handle range.
            SASSERT(expression->get_num_args() == 2);
            const auto range_begin{ expression->get_arg(0) };
            const auto range_end{ expression->get_arg(1) };
            SASSERT(is_app(range_begin));
            SASSERT(is_app(range_end));
            const auto range_begin_value{ to_app(range_begin)->get_parameter(0).get_zstring()[0] };
            const auto range_end_value{ to_app(range_end)->get_parameter(0).get_zstring()[0] };

            nfa.initial.insert(0);
            nfa.final.insert(1);
            auto current_value{ range_begin_value };
            while (current_value <= range_end_value) {
                nfa.delta.add(0, current_value, 1);
                ++current_value;
            }
        } else if (m_util_s.re.is_reverse(expression)) { // Handle reverse.
            throw_error("reverse is unsupported");
        } else if (m_util_s.re.is_union(expression)) { // Handle union (= or; A|B).
            SASSERT(expression->get_num_args() == 2);
            const auto left{ expression->get_arg(0) };
            const auto right{ expression->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            
            Mata::Nfa::Nfa aut1 {conv_to_nfa(to_app(left), m_util_s, m, alphabet, determinize)};
            Mata::Nfa::Nfa aut2 {conv_to_nfa(to_app(right), m_util_s, m, alphabet, determinize)};
            nfa = Mata::Nfa::uni(aut1, aut2);
            
        } else if (m_util_s.re.is_star(expression)) { // Handle star iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet, determinize);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();

            // Make new initial final in order to accept empty string as is required by kleene-star.
            State new_state = nfa.add_state();
            nfa.initial.insert(new_state);
            nfa.final.insert(new_state);

        } else if (m_util_s.re.is_plus(expression)) { // Handle positive iteration.
            SASSERT(expression->get_num_args() == 1);
            const auto child{ expression->get_arg(0) };
            SASSERT(is_app(child));
            nfa = conv_to_nfa(to_app(child), m_util_s, m, alphabet);
            for (const auto& final : nfa.final) {
                for (const auto& initial : nfa.initial) {
                    nfa.delta.add(final, Mata::Nfa::EPSILON, initial);
                }
            }
            nfa.remove_epsilon();
        } else if(m_util_s.str.is_string(expression)) { // Handle string literal.
            SASSERT(expression->get_num_parameters() == 1);
            nfa = create_word_nfa(expression->get_parameter(0).get_zstring());
        } else if(is_variable(expression, m_util_s)) { // Handle variable.
            throw_error("variable in regexes are unsupported");
        } else {
            throw_error("unsupported operation in regex");
        }

        // intermediate automata reduction
        // if the automaton is too big --> skip it. The computation of the simulation would be too expensive.
        if(nfa.size() < 1000) {
            nfa = Mata::Nfa::reduce(nfa);
        }
        if(determinize) {
            nfa = Mata::Nfa::minimize(nfa);
        }

        STRACE("str-create_nfa",
            tout << "--------------" << "NFA for: " << mk_pp(const_cast<app*>(expression), const_cast<ast_manager&>(m)) << "---------------" << std::endl;
            nfa.print_to_DOT(tout);
        );

        // Whether to create complement of the final automaton.
        // Warning: is_complement assumes we do the following, so if you to change this, go check is_complement first
        if (make_complement) {
            STRACE("str-create_nfa", tout << "Complemented NFA:" << std::endl;);
            Mata::OnTheFlyAlphabet mata_alphabet{};
            for (const auto& symbol : alphabet) {
                mata_alphabet.add_new_symbol(std::to_string(symbol), symbol);
            }
            nfa = Mata::Nfa::complement(nfa, mata_alphabet, { 
                {"algorithm", "classical"}, 
                //{"minimize", "true"} // it seems that minimizing during complement causes more TOs in benchmarks
                });
            STRACE("str-create_nfa", nfa.print_to_DOT(tout););
        }
        return nfa;
    }

    Nfa create_word_nfa(const zstring& word) {
        const size_t word_length{ word.length() };
        Mata::Nfa::Nfa nfa{ word_length, { 0 }, { word_length } };
        nfa.initial.insert(0);
        size_t state{ 0 };
        for (; state < word.length(); ++state) {
            nfa.delta.add(state, word[state], state + 1);
        }
        nfa.final.insert(state);
        return nfa;
    }

    void collect_terms(app* const ex, ast_manager& m, const seq_util& m_util_s, obj_map<expr, expr*>& pred_replace,
                       std::map<BasicTerm, expr_ref>& var_name, std::vector<BasicTerm>& terms) {

        if(m_util_s.str.is_string(ex)) { // Handle string literals.
            terms.emplace_back(BasicTermType::Literal, ex->get_parameter(0).get_zstring());
            return;
        }

        if(is_variable(ex, m_util_s)) {
            std::string var = ex->get_decl()->get_name().str();
            BasicTerm bvar(BasicTermType::Variable, var);
            terms.emplace_back(bvar);
            var_name.insert({bvar, expr_ref(ex, m)});
            return;
        }

        if(!m_util_s.str.is_concat(ex)) {
            expr* rpl = pred_replace.find(ex); // dies if it is not found
            collect_terms(to_app(rpl), m, m_util_s, pred_replace, var_name, terms);
            return;
        }

        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m, m_util_s, pred_replace, var_name, terms);
        collect_terms(a_y, m, m_util_s, pred_replace, var_name, terms);
    }

    BasicTerm get_variable_basic_term(expr *const variable) {
        SASSERT(is_app(variable));
        const app* variable_app{ to_app(variable) };
        SASSERT(variable_app->get_num_args() == 0);
        return BasicTerm{ BasicTermType::Variable, variable_app->get_decl()->get_name().str() };
    }

    void get_len_exprs(app* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<app>& res) {
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

    bool is_len_sub(expr* val, expr* s, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& num_res) {
        expr* num = nullptr;
        expr* len = nullptr;
        expr* str = nullptr;
        if(!m_util_a.is_add(val, num, len)) {
            return false;
        }

        if(!m_util_a.is_int(num)) {
            return false;
        }
        num_res = num;

        if(!m_util_s.str.is_length(len, str) || str->hash() != s->hash()) {
            return false;
        } 
        
        return true;
    }

    expr_ref len_to_expr(const LenNode &node, const std::map<BasicTerm, expr_ref>& variable_map, ast_manager &m, seq_util& m_util_s, arith_util& m_util_a) {
        switch(node.type) {
        case LenFormulaType::LEAF:
            if(node.atom_val.get_type() == BasicTermType::Length)
                return expr_ref(m_util_a.mk_int(std::stoi(node.atom_val.get_name().encode())), m);
            else if (node.atom_val.get_type() == BasicTermType::Literal) {
                // for literal, get the exact length of it
                return expr_ref(m_util_a.mk_int(node.atom_val.get_name().length()), m);
            } else {
                auto it = variable_map.find(node.atom_val);
                expr_ref var_expr(m);
                if(it != variable_map.end()) { // if the variable is not found, it was introduced in the preprocessing -> create a new z3 variable
                    var_expr = expr_ref(m_util_s.str.mk_length(it->second), m);
                } else {
                    var_expr = mk_int_var(node.atom_val.get_name().encode(), m, m_util_a);
                }
                return var_expr;
            }

        case LenFormulaType::PLUS: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(0), m);
            expr_ref plus = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                plus = m_util_a.mk_add(plus, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return plus;
        }

        case LenFormulaType::TIMES: {
            if (node.succ.size() == 0)
                return expr_ref(m_util_a.mk_int(1), m);
            expr_ref times = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                times = m_util_a.mk_mul(times, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return times;
        }

        case LenFormulaType::EQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m_util_a.mk_eq(left, right), m);
        }

        case LenFormulaType::NEQ: {
            assert(node.succ.size() == 2);
            expr_ref left = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            expr_ref right = len_to_expr(node.succ[1], variable_map, m, m_util_s, m_util_a);
            return expr_ref(m.mk_not(m_util_a.mk_eq(left, right)), m);
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

        case LenFormulaType::OR: {
            if(node.succ.size() == 0)
                return expr_ref(m.mk_false(), m);
            expr_ref orref = len_to_expr(node.succ[0], variable_map, m, m_util_s, m_util_a);
            for(size_t i = 1; i < node.succ.size(); i++) {
                orref = m.mk_or(orref, len_to_expr(node.succ[i], variable_map, m, m_util_s, m_util_a));
            }
            return orref;
        }

        case LenFormulaType::TRUE: {
            return expr_ref(m.mk_true(), m);
        }

        case LenFormulaType::FALSE: {
            return expr_ref(m.mk_false(), m);
        }

        default:
            throw_error("Unexpected length formula type");
            return {{}, m};
        }
    }
}
