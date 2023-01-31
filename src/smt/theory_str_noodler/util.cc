#include <cassert>
#include <mata/re2parser.hh>

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using Mata::Nfa::Nfa;
}

namespace smt::noodler::util {
    void extract_symbols(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet) {
        if (m_util_s.str.is_string(ex)) {
            auto ex_app{ to_app(ex) };
            SASSERT(ex_app->get_num_args() == 1);
            const zstring string_literal{ zstring{ ex_app->get_parameter(0).get_zstring() } };
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                alphabet.insert(string_literal[i]);
            }
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) { // Skip variables.
            return;
        }

        SASSERT(is_app(ex));
        app* ex_app = to_app(ex);

        if (m_util_s.re.is_to_re(ex_app)) { // Handle conversion to regex function call.
            // Assume that expression inside re.to_re() function is a string of characters.
            SASSERT(ex_app->get_num_args() == 1);
            const auto arg{ ex_app->get_arg(0) };
            //SASSERT(is_string_sort(arg));
            extract_symbols(to_app(arg), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app)) { // Handle concatenation.
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ex_app->get_arg(0)};
            const auto right{ex_app->get_arg(1)};
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union.
            assert(false && "re.is_antimirov_union(ex_app)");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement.
            assert(false && "re.is_complement(ex_app)");
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative.
            assert(false && "re.is_derivative(ex_app)");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff.
            assert(false && "re.is_diff(ex_app)");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus.
            assert(false && "re.is_dot_plus(ex_app)");
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty string.
            assert(false && "re.is_empty(ex_app)");
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon.
            assert(false && "re.is_epsilon(ex_app)");
        } else if (m_util_s.re.is_full_char(ex_app)) { // Handle full char.
            assert(false && "re.is_full_char(ex_app)");
        } else if (m_util_s.re.is_full_seq(ex_app)) { // Handle full sequence (any character, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_intersection(ex_app)) { // Handle intersection.
            assert(false && "re.is_intersection(ex_app)");
        } else if (m_util_s.re.is_loop(ex_app)) { // Handle loop.
            assert(false && "re.is_loop(ex_app)");
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate.
            assert(false && "re.is_of_pred(ex_app)");
        } else if (m_util_s.re.is_opt(ex_app)) { // Handle optional.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range.
            assert(false && "re.is_range(ex_app)");
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse.
            assert(false && "re.is_reverse(ex_app)");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            extract_symbols(to_app(left), m_util_s, m, alphabet);
            extract_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_star(ex_app)) { // Handle star iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_plus(ex_app)) { // Handle positive iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            extract_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if(is_app(ex_app) && to_app(ex_app)->get_num_args() == 0) { // Handle variable.
            assert(false && "is_variable(ex_app)");
        }

        // When ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            extract_symbols(arg, m_util_s, m, alphabet);
        }
    }

    void get_variables(expr* const ex, const seq_util& m_util_s, const ast_manager& m, obj_hashtable<expr>& res) {
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

    void get_variable_names(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::unordered_set<std::string>& res) {
        if(m_util_s.str.is_string(ex)) {
            return;
        }

        if(is_app(ex) && to_app(ex)->get_num_args() == 0) {
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

    std::set<uint32_t> get_dummy_symbols(const vector<expr_pair>& disequations, std::set<uint32_t>& symbols_to_append_to) {
        std::set<uint32_t> dummy_symbols{};
        uint32_t dummy_symbol{ 0 };
        const size_t disequations_number{ disequations.size() };
        for (size_t diseq_index{ 0 }; diseq_index < disequations_number; ++diseq_index) {
            while (symbols_to_append_to.find(dummy_symbol) != symbols_to_append_to.end()) { ++dummy_symbol; }
            dummy_symbols.insert(dummy_symbol);
            ++dummy_symbol;
        }
        const size_t dummy_symbols_number{ dummy_symbols.size() };
        assert(dummy_symbols_number == disequations_number);
        const size_t symbols_in_formula_number{ symbols_to_append_to.size() };
        symbols_to_append_to.insert(dummy_symbols.begin(), dummy_symbols.end());
        assert(dummy_symbols_number + symbols_in_formula_number == symbols_to_append_to.size());
        return dummy_symbols;
    }

    std::set<uint32_t> get_symbols_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const seq_util& m_util_s,
            const ast_manager& m
    ) {
        std::set<uint32_t> symbols_in_formula{};
        for (const auto &word_equation: equations) {
            util::extract_symbols(word_equation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_equation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &word_equation: disequations) {
            util::extract_symbols(word_equation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_equation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &word_equation: regexes) {
            util::extract_symbols(std::get<1>(word_equation), m_util_s, m, symbols_in_formula);
        }
        return symbols_in_formula;
    }

    AutAssignment create_aut_assignment_for_formula(
            const vector<expr_pair>& equations,
            const vector<expr_pair>& disequations,
            const vector<expr_pair_flag>& regexes,
            const seq_util& m_util_s,
            const ast_manager& m,
            const std::set<uint32_t>& alphabet
    ) {
        // Find all variables in the whole formula.
        std::unordered_set<std::string> variables_in_formula{};
        for (const auto &word_equation: equations) {
            util::get_variable_names(word_equation.first, m_util_s, m, variables_in_formula);
            util::get_variable_names(word_equation.second, m_util_s, m, variables_in_formula);
        }
        for (const auto &word_equation: disequations) {
            util::get_variable_names(word_equation.first, m_util_s, m, variables_in_formula);
            util::get_variable_names(word_equation.second, m_util_s, m, variables_in_formula);
        }

        // DEBUG.
        std::cout << "Variable names:\n";
        for (const auto& name : variables_in_formula) {
            std::cout << name << "\n";
        }

        AutAssignment aut_assignment{};
        // Create automata from their corresponding regexes.
        std::unordered_set<std::string> variables_with_regex{};
        for (const auto &word_equation: regexes) {
            const auto& variable{ std::get<0>(word_equation) };
            assert(is_app(variable));
            const auto& variable_app{ to_app(variable) };
            assert(variable_app->get_num_args() == 0);
            const auto& variable_name{ variable_app->get_decl()->get_parameter(0).get_symbol().str() };
            variables_with_regex.insert(variable_name);
            BasicTerm variable_term{ BasicTermType::Variable, variable_name };
            assert(aut_assignment.find(variable_term) == aut_assignment.end());
            Nfa nfa{};
            Mata::RE2Parser::create_nfa(&nfa, conv_to_regex_hex(to_app(std::get<1>(word_equation)), m_util_s, m, alphabet));
            aut_assignment[variable_term] = std::make_shared<Nfa>(std::forward<Nfa>(std::move(nfa)));
        }

        // Assign sigma start automata for all yet unassigned variables.
        const Nfa nfa_sigma_star{ aut_assignment.sigma_star_automaton() };
        for (const auto& variable_name : variables_in_formula) {
            if (variables_with_regex.find(variable_name) == variables_with_regex.end()) {
                BasicTerm variable_term{ BasicTermType::Variable, variable_name };
                assert(aut_assignment.find(variable_term) == aut_assignment.end());
                aut_assignment[variable_term] = std::make_shared<Nfa>(nfa_sigma_star);
            }
        }

        return aut_assignment;
    }

    std::string conv_to_regex_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m, const std::set<uint32_t>& alphabet) {
        std::string regex{};
        if (m_util_s.re.is_to_re(expr)) { // Handle conversion to regex function call.
            // Assume that expression inside re.to_re() function is a string of characters.
            SASSERT(expr->get_num_args() == 1);
            const auto arg{ expr->get_arg(0) };
            regex = conv_to_regex_hex(to_app(arg), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_concat(expr)) { // Handle concatenation.
            SASSERT(expr->get_num_args() == 2);
            const auto left{expr->get_arg(0)};
            const auto right{expr->get_arg(1)};
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            regex = conv_to_regex_hex(to_app(left), m_util_s, m, alphabet) + conv_to_regex_hex(to_app(right), m_util_s, m, alphabet);
        } else if (m_util_s.re.is_antimirov_union(expr)) { // Handle Antimirov union.
            assert(false && "re.is_antimirov_union(expr)");
        } else if (m_util_s.re.is_complement(expr)) { // Handle complement.
            assert(false && "re.is_complement(expr)");
        } else if (m_util_s.re.is_derivative(expr)) { // Handle derivative.
            assert(false && "re.is_derivative(expr)");
        } else if (m_util_s.re.is_diff(expr)) { // Handle diff.
            assert(false && "re.is_diff(expr)");
        } else if (m_util_s.re.is_dot_plus(expr)) { // Handle dot plus.
            assert(false && "re.is_dot_plus(expr)");
        } else if (m_util_s.re.is_empty(expr)) { // Handle empty string.
            assert(false && "re.is_empty(expr)");
        } else if (m_util_s.re.is_epsilon(expr)) { // Handle epsilon.
            assert(false && "re.is_epsilon(expr)");
        } else if (m_util_s.re.is_full_char(expr)) { // Handle full char.
            assert(false && "re.is_full_char(expr)");
        } else if (m_util_s.re.is_full_seq(expr)) { // Handle full sequence (any character, '.') (SMT2: re.allchar).
            regex += "[";
            std::stringstream convert_stream;
            for (const auto& symbol : alphabet) {
                convert_stream << std::dec << "\\x{" << std::hex << symbol << std::dec << "}";
            }
            regex += convert_stream.str();
            regex += "]";
        } else if (m_util_s.re.is_intersection(expr)) { // Handle intersection.
            assert(false && "re.is_intersection(expr)");
        } else if (m_util_s.re.is_loop(expr)) { // Handle loop.
            assert(false && "re.is_loop(expr)");
        } else if (m_util_s.re.is_of_pred(expr)) { // Handle of predicate.
            assert(false && "re.is_of_pred(expr)");
        } else if (m_util_s.re.is_opt(expr)) { // Handle optional.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")?";
        } else if (m_util_s.re.is_range(expr)) { // Handle range.
            assert(false && "re.is_range(expr)");
        } else if (m_util_s.re.is_reverse(expr)) { // Handle reverse.
            assert(false && "re.is_reverse(expr)");
        } else if (m_util_s.re.is_union(expr)) { // Handle union (= or; A|B).
            SASSERT(expr->get_num_args() == 2);
            const auto left{ expr->get_arg(0) };
            const auto right{ expr->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            regex = "(" + conv_to_regex_hex(to_app(left), m_util_s, m, alphabet) + ")|(" + conv_to_regex_hex(to_app(right), m_util_s, m, alphabet) + ")";
        } else if (m_util_s.re.is_star(expr)) { // Handle star iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")*";
        } else if (m_util_s.re.is_plus(expr)) { // Handle positive iteration.
            SASSERT(expr->get_num_args() == 1);
            const auto child{ expr->get_arg(0) };
            SASSERT(is_app(child));
            regex = "(" + conv_to_regex_hex(to_app(child), m_util_s, m, alphabet) + ")+";
        } else if(m_util_s.str.is_string(expr)) { // Handle string literal.
            SASSERT(expr->get_num_args() == 1);
            const zstring string_literal{ zstring{ expr->get_parameter(0).get_zstring().encode() } };
            std::stringstream convert_stream;
            for (size_t i{ 0 }; i < string_literal.length(); ++i) {
                convert_stream << std::dec << "\\x{" << std::hex << string_literal[i] << std::dec << "}";
            }
            regex = convert_stream.str();
        } else if(is_app(expr) && to_app(expr)->get_num_args() == 0) { // Handle variable.
            assert(false && "is_variable(expr)");
        }
        return regex;
    }

    void collect_terms(const app* ex, const seq_util& m_util_s, std::vector<BasicTerm>& terms) {
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

        SASSERT(m_util_s.str.is_concat(ex));
        SASSERT(ex->get_num_args() == 2);
        app *a_x = to_app(ex->get_arg(0));
        app *a_y = to_app(ex->get_arg(1));
        collect_terms(a_x, m_util_s, terms);
        collect_terms(a_y, m_util_s, terms);
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
}
