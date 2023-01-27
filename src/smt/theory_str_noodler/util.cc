#include <cassert>

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"

namespace smt::noodler::util {
    void get_symbols(expr* const ex, const seq_util& m_util_s, const ast_manager& m, std::set<uint32_t>& alphabet) {
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
            get_symbols(to_app(arg), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_concat(ex_app)) { // Handle concatenation.
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ex_app->get_arg(0)};
            const auto right{ex_app->get_arg(1)};
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            get_symbols(to_app(left), m_util_s, m, alphabet);
            get_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_antimirov_union(ex_app)) { // Handle Antimirov union. // TODO: What is this?
            assert(false && "re.is_antimirov_union(ex_app)");
        } else if (m_util_s.re.is_complement(ex_app)) { // Handle complement. // TODO: What is this?
            assert(false && "re.is_complement(ex_app)");
        } else if (m_util_s.re.is_derivative(ex_app)) { // Handle derivative. // TODO: What is this?
            assert(false && "re.is_derivative(ex_app)");
        } else if (m_util_s.re.is_diff(ex_app)) { // Handle diff. // TODO: What is this?
            assert(false && "re.is_diff(ex_app)");
        } else if (m_util_s.re.is_dot_plus(ex_app)) { // Handle dot plus. // TODO: What is this?
            assert(false && "re.is_dot_plus(ex_app)");
        } else if (m_util_s.re.is_empty(ex_app)) { // Handle empty string. // TODO: What is this?
            assert(false && "re.is_empty(ex_app)");
        } else if (m_util_s.re.is_epsilon(ex_app)) { // Handle epsilon. // TODO: Maybe ignore completely.
            assert(false && "re.is_epsilon(ex_app)");
        } else if (m_util_s.re.is_full_char(ex_app)) { // Handle full char. // TODO: What is this?
            assert(false && "re.is_full_char(ex_app)");
        } else if (m_util_s.re.is_full_seq(ex_app)) { // Handle full sequence (any character, '.') (SMT2: re.allchar).
            return;
        } else if (m_util_s.re.is_intersection(ex_app)) { // Handle intersection. // TODO: What is this?
            assert(false && "re.is_intersection(ex_app)");
        } else if (m_util_s.re.is_loop(ex_app)) { // Handle loop. // TODO: What is this?
            assert(false && "re.is_loop(ex_app)");
        } else if (m_util_s.re.is_of_pred(ex_app)) { // Handle of predicate. // TODO: What is this?
            assert(false && "re.is_of_pred(ex_app)");
        } else if (m_util_s.re.is_opt(ex_app)) { // Handle optional.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            get_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_range(ex_app)) { // Handle range. // TODO: What is this?
            assert(false && "re.is_range(ex_app)");
        } else if (m_util_s.re.is_reverse(ex_app)) { // Handle reverse. // TODO: What is this?
            assert(false && "re.is_reverse(ex_app)");
        } else if (m_util_s.re.is_union(ex_app)) { // Handle union (= or; A|B).
            SASSERT(ex_app->get_num_args() == 2);
            const auto left{ ex_app->get_arg(0) };
            const auto right{ ex_app->get_arg(1) };
            SASSERT(is_app(left));
            SASSERT(is_app(right));
            get_symbols(to_app(left), m_util_s, m, alphabet);
            get_symbols(to_app(right), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_star(ex_app)) { // Handle star iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            get_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if (m_util_s.re.is_plus(ex_app)) { // Handle positive iteration.
            SASSERT(ex_app->get_num_args() == 1);
            const auto child{ ex_app->get_arg(0) };
            SASSERT(is_app(child));
            get_symbols(to_app(child), m_util_s, m, alphabet);
            return;
        } else if(is_app(ex_app) && to_app(ex_app)->get_num_args() == 0) { // Handle variable.
            assert(false && "is_variable(ex_app)");
            // TODO: How to represent variables?
            //SASSERT(ex_app->get_num_args() == 1);
            // TODO: What if valid variable is only the first symbol, the rest is undefined from underlying variant?
            //regex = "(" + ex_app->get_decl()->get_parameter(0).get_symbol().str() + ")";
        }

        // WHen ex is not string literal, variable, nor regex, recursively traverse the AST to find symbols.
        for(unsigned i = 0; i < ex_app->get_num_args(); i++) {
            SASSERT(is_app(ex_app->get_arg(i)));
            app *arg = to_app(ex_app->get_arg(i));
            get_symbols(arg, m_util_s, m, alphabet);
        }
    }

    std::string conv_to_regex_hex(const app *expr, const seq_util& m_util_s, const ast_manager& m,  const std::set<uint32_t>& alphabet) {
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
        } else if (m_util_s.re.is_epsilon(expr)) { // Handle epsilon. // TODO: Maybe ignore completely.
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
            // TODO: How to represent variables?
            //SASSERT(expr->get_num_args() == 1);
            // TODO: What if valid variable is only the first symbol, the rest is undefined from underlying variant?
            //regex = expr->get_decl()->get_parameter(0).get_symbol().str();
        }
        return regex;
    }
}
