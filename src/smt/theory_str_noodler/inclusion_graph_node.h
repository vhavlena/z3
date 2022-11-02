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

namespace smt {
    enum struct EquationTermType {
        Literal,
        Variable,
        CallPredicate,
    };

    class BasicEquationTerm {
    public:
        //BasicEquationTerm() = default;
        BasicEquationTerm(BasicEquationTerm&) = delete;
        BasicEquationTerm(BasicEquationTerm&&) = default;

        [[nodiscard]] virtual EquationTermType get_type() const = 0;
        [[nodiscard]] virtual bool equals(const BasicEquationTerm& other) const { return get_type() == other.get_type(); }
    protected:
    }; // Class BasicEquationTerm.

    bool operator==(const BasicEquationTerm& lhs, const BasicEquationTerm& rhs) { return lhs.equals(rhs); }

    using EquationSide = std::vector<std::unique_ptr<BasicEquationTerm>>;

    class LiteralTerm : BasicEquationTerm {
        LiteralTerm() = default;
        //LiteralTerm(LiteralTerm&) = delete;
        //LiteralTerm(LiteralTerm&&) = default;
        [[nodiscard]] EquationTermType get_type() const override { return EquationTermType::Literal; }

        [[nodiscard]] bool equals(const BasicEquationTerm& other) const override {
            if (BasicEquationTerm::equals(other)) {
                // TODO: Type specific comparison.
                return true;
            }
            return false;
        }
    }; // Class LiteralTerm.

    class VariableTerm : BasicEquationTerm {
        VariableTerm() = default;
        //VariableTerm(VariableTerm&) = delete;
        //VariableTerm(VariableTerm&&) = default;
        [[nodiscard]] EquationTermType get_type() const override { return EquationTermType::Variable; }

        [[nodiscard]] bool equals(const BasicEquationTerm& other) const override {
            if (BasicEquationTerm::equals(other)) {
                // TODO: Type specific comparison.
                return true;
            }
            return false;
        }
    }; // Class VariableTerm.

    class CallPredicateTerm : BasicEquationTerm {
        CallPredicateTerm() = default;
        //CallPredicateTerm(CallPredicateTerm&) = delete;
        //CallPredicateTerm(CallPredicateTerm&&) = default;
        [[nodiscard]] EquationTermType get_type() const override { return EquationTermType::CallPredicate; }

        [[nodiscard]] bool equals(const BasicEquationTerm& other) const override {
            if (BasicEquationTerm::equals(other)) {
                // TODO: Type specific comparison.
                return true;
            }
            return false;
        }
    }; // Class CallPredicateTerm.

    class Equation {
    public:

        enum struct EquationSideType {
            Left,
            Right,
        };

        Equation(): left_side(), right_side() {}

        // TODO: Use std::move?
        Equation(EquationSide left_side, EquationSide right_side)
            : left_side(std::move(left_side)), right_side(std::move(right_side)) {}

        Equation(const Equation& equation) = delete;
        Equation(Equation&&) = default;

        void set_side(EquationSideType side, EquationSide side_value) {
            switch (side) {
                case EquationSideType::Left:
                    left_side = std::move(side_value);
                    break;
                case EquationSideType::Right:
                    right_side = std::move(side_value);
                    break;
                default:
                    throw std::runtime_error("unhandled equation side type");
                    break;
            }
        }

        EquationSide& get_side(EquationSideType side) {
            switch (side) {
                case EquationSideType::Left:
                    return left_side;
                    break;
                case EquationSideType::Right:
                    return right_side;
                    break;
                default:
                    throw std::runtime_error("unhandled equation side type");
                    break;
            }
        }

        // TODO: Should we implement get_vars() and get_side_vars()?

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

        friend bool operator==(const Equation& lhs, const Equation& rhs) {
            return lhs.left_side == rhs.left_side && lhs.right_side == rhs.right_side;
        }

        // TODO: Additional operations.

    private:
        EquationSide left_side;
        EquationSide right_side;
    }; // Class Equation.

    using FormulaEquations = std::vector<Equation>;

    class Formula {
        Formula(): equations(), inequations() {}

        FormulaEquations& get_equations() { return equations; }
        FormulaEquations& get_inequations() { return inequations; }

        // TODO: Use std::move for both add functions?
        void add_equation(Equation equation) { equations.push_back(std::move(equation)); }
        void add_inequation(Equation inequation) { inequations.push_back(std::move(inequation)); }

    private:
        FormulaEquations equations;
        FormulaEquations inequations;
    }; // Class Formula.
} // Namespace smt.

#endif //Z3_INCLUSION_GRAPH_NODE_H
