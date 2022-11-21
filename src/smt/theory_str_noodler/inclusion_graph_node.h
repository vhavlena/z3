/**
 * @brief Create basic representation of an inclusion graph node.
 *
 * The inclusion graph node is represented as a predicate, represention an equation, inequation or another predicate
 *  such as contains, etc.
 * Each equation or inequation consists of a left and right side of the equation which hold a vector of basic equation
 *  terms.
 * Each term is of one of the following types:
 *     - Literal,
 *     - Variable, or
 *     - operation such as IndexOf, Length, etc.
 */

#ifndef Z3_INCLUSION_GRAPH_NODE_H
#define Z3_INCLUSION_GRAPH_NODE_H

#include <utility>
#include <vector>
#include <stdexcept>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <string>
#include <string_view>

namespace smt::noodler {
    enum struct PredicateType {
        Equation,
        Inequation,
        Contains,
        // TODO: Add additional predicate types.
    };

    enum struct BasicTermType {
        Literal,
        Variable,
        Length,
        Substring,
        IndexOf,
        // TODO: Add additional basic term types.
    };

    class BasicTerm {
    public:
        explicit BasicTerm(BasicTermType type): type(type) {}
        BasicTerm(BasicTermType type, std::string_view name): type(type), name(name) {}

        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] bool is_variable() const { return type == BasicTermType::Variable; }
        [[nodiscard]] bool is_literal() const { return type == BasicTermType::Literal; }
        [[nodiscard]] bool is(BasicTermType term_type) const { return type == term_type; }

        [[nodiscard]] std::string get_name() const { return name; }
        void set_name(std::string_view new_name) { name = new_name; }

        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

    private:
        BasicTermType type;
        std::string name;
    }; // Class BasicTerm.

    static bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }

    class Predicate {
    public:
        enum struct EquationSideType {
            Left,
            Right,
        };

        explicit Predicate(const PredicateType type): type(type) {
            if (is_equation() || is_inequation()) {
                params.resize(2);
                params.emplace_back();
                params.emplace_back();
            }
        }

        explicit Predicate(const PredicateType type, std::vector<std::vector<BasicTerm>> par): 
            type(type), 
            params(par) 
            { }

        PredicateType get_type() { return type; }
        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_eq_or_ineq() const { return is_equation() || is_inequation(); }
        [[nodiscard]] bool is_predicate() const { return !is_eq_or_ineq(); }
        [[nodiscard]] bool is(const PredicateType predicate_type) const { return predicate_type == this->type; }

        std::vector<BasicTerm>& get_left_side() {
            assert(is_eq_or_ineq());
            return params[0];
        }

        [[nodiscard]] const std::vector<BasicTerm>& get_left_side() const {
            assert(is_eq_or_ineq());
            return params[0];
        }

        std::vector<BasicTerm>& get_right_side() {
            assert(is_eq_or_ineq());
            return params[1];
        }

        [[nodiscard]] const std::vector<BasicTerm>& get_right_side() const {
            assert(is_eq_or_ineq());
            return params[1];
        }

        std::vector<BasicTerm>& get_side(const EquationSideType side) {
            assert(is_eq_or_ineq());
            switch (side) {
                case EquationSideType::Left:
                    return params[0];
                    break;
                case EquationSideType::Right:
                    return params[1];
                    break;
                default:
                    throw std::runtime_error("unhandled equation side type");
                    break;
            }
        }

        [[nodiscard]] const std::vector<BasicTerm>& get_side(const EquationSideType side) const {
            assert(is_eq_or_ineq());
            switch (side) {
                case EquationSideType::Left:
                    return params[0];
                    break;
                case EquationSideType::Right:
                    return params[1];
                    break;
                default:
                    throw std::runtime_error("unhandled equation side type");
                    break;
            }
        }

        /**
         * Get unique variables on both sides of an (in)equation.
         * @return Variables in the (in)equation.
         */
        [[nodiscard]] std::vector<BasicTerm> get_vars() const {
            assert(is_eq_or_ineq());
            std::vector<BasicTerm> vars;
            for (const auto& side: params) {
                for (const auto &term: side) {
                    if (term.is_variable()) {
                        bool found{false};
                        for (const auto &var: vars) {
                            if (var == term) {
                                found = true;
                                break;
                            }
                        }
                        if (!found) { vars.push_back(term); }
                    }
                }
            }
            return vars;
        }

        /**
         * Get unique variables on a single @p side of an (in)equation.
         * @param[in] side (In)Equation side to get variables from.
         * @return Variables in the (in)equation on specified @p side.
         */
        [[nodiscard]] std::vector<BasicTerm> get_side_vars(const EquationSideType side) const {
            assert(is_eq_or_ineq());
            std::vector<BasicTerm> vars;
            std::vector<BasicTerm> side_terms;
            switch (side) {
                case EquationSideType::Left:
                    side_terms = get_left_side();
                    break;
                case EquationSideType::Right:
                    side_terms = get_right_side();
                    break;
                default:
                    throw std::runtime_error("unhandled equation side_terms type");
                    break;
            }

            for (const auto &term: side_terms) {
                if (term.is_variable()) {
                    bool found{false};
                    for (const auto &var: vars) {
                        if (var == term) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) { vars.push_back(term); }
                }
            }
           return vars;
        }

        /**
         * Decide whether the @p side contains multiple occurrences of a single variable (with a same name).
         * @param side Side to check.
         * @return True if there are multiple occurrences of a single variable. False otherwise.
         */
        [[nodiscard]] bool mult_occurr_var_side(const EquationSideType side) const {
            assert(is_eq_or_ineq());
            const auto terms_begin{ get_side(side).cbegin() };
            const auto terms_end{ get_side(side).cend() };
            for (auto term_iter{ terms_begin }; term_iter < terms_end; ++term_iter) {
                if (term_iter->is_variable()) {
                    for (auto term_iter_following{ term_iter + 1}; term_iter_following < terms_end;
                         ++term_iter_following) {
                        if (*term_iter == *term_iter_following) {
                            return true;
                            // TODO: How to handle calls of predicates?
                        }
                    }
                }
            }
            return false;
        }

        void replace(void* replace_map) {
            (void) replace_map;
            throw std::runtime_error("unimplemented");
        }

        void remove(void* terms_to_remove) {
            (void) terms_to_remove;
            throw std::runtime_error("unimplemented");
        }

        [[nodiscard]] bool equals(const Predicate& other) const {
            if (type == other.type) {
                if (is_eq_or_ineq()) {
                    return params[0] == other.params[0] && params[1] == other.params[1];
                }
                return true;
            }
            return false;
        }

        // TODO: Additional operations.

    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params;
    }; // Class Predicate.

    static bool operator==(const Predicate& lhs, const Predicate& rhs) { return lhs.equals(rhs); }

    class Formula {
    
    public:
        Formula(): predicates() {}

        std::vector<Predicate>& get_predicates() { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(const Predicate& predicate) { predicates.push_back(predicate); }

    private:
        std::vector<Predicate> predicates;
    }; // Class Formula.
} // Namespace smt::noodler.

#endif //Z3_INCLUSION_GRAPH_NODE_H
