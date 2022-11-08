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

namespace smt {
namespace noodler {
    enum struct EquationTermType {
        Literal,
        Variable,
        CallPredicate,
    };

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
        BasicTerm(const std::string& name, BasicTermType type): name(name), type(type) {}
        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] const std::string& get_name() const { return name; }
        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

    private:
        std::string name;
        BasicTermType type;
    }; // Class BasicEquationTerm.

    bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }

    class Predicate {
    public:
        enum struct EquationSideType {
            Left,
            Right,
        };

        explicit Predicate(const PredicateType type): type(type) {}

        PredicateType get_type() { return type; }
        void set_type(PredicateType new_type) { type = new_type; }

        std::vector<BasicTerm>& get_left() {
            assert(type == PredicateType::Equation || type == PredicateType::Inequation);
            return params[0];
        }
        std::vector<BasicTerm>& get_right() { return params[0]; }

        // TODO: Should we implement get_vars() and get_side_vars()?

        std::vector<BasicTerm>& get_side(EquationSideType side) {
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

        bool multiple_occurrence_of_term_on_side(EquationSideType side) {
            (void) side;
            throw std::runtime_error("unimplemented");
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
            return lhs.type == rhs.type; // FIXME: Compare sides (both left and right sides).
        }

        // TODO: Additional operations.

    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params{};

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
