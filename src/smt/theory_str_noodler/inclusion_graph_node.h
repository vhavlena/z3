/**
 * @brief Create basic representation of inclusion graph node
 *
 * The inclusion graph node is represented as a formula consisting of equations and ineqautions.
 * Each equation or inequation consists of a left and right side of the equation which hold a vector of basic equations
 *  terms.
 * Each term is of one of the following types:
 *     - Literal,
 *     - Variable, or
 *     - CallPredicate.
 */
#ifndef Z3_INCLUSION_GRAPH_NODE_H
#define Z3_INCLUSION_GRAPH_NODE_H

#include <utility>
#include <vector>
#include <stdexcept>
#include <memory>
#include <cassert>
#include <unordered_map>

namespace smt {
namespace noodler {
    enum struct PredicateType {
        Equation,
        Inequation,
        Substring,
        Contains,
        Length,
        IndexOf,
        // TODO: Add additional predicate types.
    };

    enum struct BasicTermType {
        Literal,
        Variable
    };

    class BasicTerm {
    public:
        explicit BasicTerm(BasicTermType type): type(type) {}
        BasicTerm(BasicTermType type, std::string_view name): type(type), name(name) {}
        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] std::string get_name() const { return name; }
        void set_name(std::string_view new_name) { name = new_name; }
        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

    private:
        BasicTermType type;
        std::string name;
    }; // Class BasicTerm.

    bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }

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

        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_predicate() const { return !is_equation() && !is_inequation(); }

        PredicateType get_type() { return type; }
        void set_type(PredicateType new_type) { type = new_type; }

        std::vector<BasicTerm>& get_left() {
            assert(is_equation() || is_inequation());
            return params[0];
        }
        std::vector<BasicTerm>& get_right() {
            assert(is_equation() || is_inequation());
            return params[1];
        }

        // TODO: Should we implement get_vars() and get_side_vars()?

        std::vector<BasicTerm>& get_side(const EquationSideType side) {
            assert(is_equation() || is_inequation());
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

        bool multiple_occurrence_of_term_on_side(const EquationSideType side) {
            assert(is_equation() || is_inequation());
            const auto terms_begin{ get_side(side).cbegin() };
            const auto terms_end{ get_side(side).cend() };
            for (auto term_iter{ terms_begin }; term_iter < terms_end; ++term_iter) {
                for (auto term_iter_following{ term_iter + 1}; term_iter_following < terms_end; ++term_iter_following) {
                    if (*term_iter == *term_iter_following) {
                        return true;
                        // TODO: How to handle calls of predicates?
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

        friend bool operator==(const Predicate& lhs, const Predicate& rhs) {
            if (lhs.type == rhs.type) {
                if (lhs.is_equation() || lhs.is_inequation()) {
                    return lhs.params[0] == rhs.params[0] && lhs.params[1] == rhs.params[1];
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

    using FormulaPredicates = std::vector<Predicate>;

    class Formula {
        Formula(): predicates() {}

        FormulaPredicates& get_predicates() { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(const Predicate& predicate) { predicates.push_back(predicate); }

    private:
        FormulaPredicates predicates;
    }; // Class Formula.
} // Namespace noodler.
} // Namespace smt.

#endif //Z3_INCLUSION_GRAPH_NODE_H
