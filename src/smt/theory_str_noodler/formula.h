/**
 * @brief Create basic representation of firnzkae.
 *
 * Each equation or inequation consists of a left and right side of the equation which hold a vector of basic equation
 *  terms.
 * Each term is of one of the following types:
 *     - Literal,
 *     - Variable, or
 *     - operation such as IndexOf, Length, etc.
 */

#ifndef Z3_NOODLER_FORMULA_H
#define Z3_NOODLER_FORMULA_H

#include <utility>
#include <vector>
#include <stdexcept>
#include <memory>
#include <cassert>
#include <unordered_map>
#include <string>
#include <string_view>
#include <set>
#include <unordered_set>
#include <iostream>
#include "util/zstring.h"

namespace smt::noodler {
    enum struct PredicateType {
        Default,
        Equation,
        Inequation,
        Contains,
        // TODO: Add additional predicate types.
    };

    [[nodiscard]] static std::string to_string(PredicateType predicate_type) {
        switch (predicate_type) {
            case PredicateType::Default:
                return "Default";
            case PredicateType::Equation:
                return "Equation";
            case PredicateType::Inequation:
                return "Inequation";
            case PredicateType::Contains:
                return "Contains";
        }

        throw std::runtime_error("Unhandled predicate type passed to to_string().");
    }

    enum struct BasicTermType {
        Variable,
        Literal,
        Length,
        Substring,
        IndexOf,
        Lang,
        // TODO: Add additional basic term types.
    };

    [[nodiscard]] static std::string to_string(BasicTermType term_type) {
        switch (term_type) {
            case BasicTermType::Variable:
                return "Variable";
            case BasicTermType::Literal:
                return "Literal";
            case BasicTermType::Length:
                return "Length";
            case BasicTermType::Substring:
                return "Substring";
            case BasicTermType::IndexOf:
                return "IndexOf";
            case BasicTermType::Lang:
                return "Lang";
        }

        throw std::runtime_error("Unhandled basic term type passed to to_string().");
    }

    class BasicTerm {
    public:
        explicit BasicTerm(BasicTermType type): type(type) {}
        BasicTerm(BasicTermType type, zstring name): type(type), name(std::move(name)) {}

        [[nodiscard]] BasicTermType get_type() const { return type; }
        [[nodiscard]] bool is_variable() const { return type == BasicTermType::Variable; }
        [[nodiscard]] bool is_literal() const { return type == BasicTermType::Literal; }
        [[nodiscard]] bool is(BasicTermType term_type) const { return type == term_type; }

        [[nodiscard]] zstring get_name() const { return name; }
        void set_name(zstring new_name) { name = std::move(new_name); }

        [[nodiscard]] bool equals(const BasicTerm& other) const {
            return type == other.get_type() && name == other.get_name();
        }

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator() (const BasicTerm& basic_term) const {
                size_t row_hash = std::hash<BasicTermType>()(basic_term.type);
                size_t col_hash = basic_term.name.hash() << 1;
                return row_hash ^ col_hash;
            }
        };

    private:
        BasicTermType type;
        // name of the variable, or the given literal
        zstring name;
    }; // Class BasicTerm.

    [[nodiscard]] static std::string to_string(const BasicTerm& basic_term) {
        return basic_term.to_string();
    }

    static bool operator==(const BasicTerm& lhs, const BasicTerm& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs == rhs); }
    static bool operator<(const BasicTerm& lhs, const BasicTerm& rhs) {
        if (lhs.get_type() < rhs.get_type()) {
            return true;
        } else if (lhs.get_type() > rhs.get_type()) {
            return false;
        }
        // Types are equal. Compare names.
        if (lhs.get_name() < rhs.get_name()) {
            return true;
        }
        return false;
    }
    static bool operator>(const BasicTerm& lhs, const BasicTerm& rhs) { return !(lhs < rhs); }

    //----------------------------------------------------------------------------------------------------------------------------------

    enum struct LenFormulaType {
        PLUS,
        EQ,
        NOT,
        LEQ,
        LEAF,
        AND,
        TRUE,
        FALSE,
    };

    struct LenNode {
        LenFormulaType type;
        BasicTerm atom_val;
        std::vector<struct LenNode> succ;

        LenNode(LenFormulaType tp, BasicTerm val, std::vector<struct LenNode> s) : type(tp), atom_val(val), succ(s) { };
        LenNode(LenFormulaType tp, std::vector<struct LenNode> s) : type(tp), atom_val(BasicTerm(BasicTermType::Length)), succ(s) { };

    };

    //----------------------------------------------------------------------------------------------------------------------------------

    class Predicate {
    public:
        enum struct EquationSideType {
            Left,
            Right,
        };

        Predicate() : type(PredicateType::Default) {}
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

        [[nodiscard]] PredicateType get_type() const { return type; }
        [[nodiscard]] bool is_equation() const { return type == PredicateType::Equation; }
        [[nodiscard]] bool is_inequation() const { return type == PredicateType::Inequation; }
        [[nodiscard]] bool is_eq_or_ineq() const { return is_equation() || is_inequation(); }
        [[nodiscard]] bool is_predicate() const { return !is_eq_or_ineq(); }
        [[nodiscard]] bool is(const PredicateType predicate_type) const { return predicate_type == this->type; }

        const std::vector<std::vector<BasicTerm>>& get_params() const { return this->params; }

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

        void set_left_side(const std::vector<BasicTerm> &new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = new_left_side;
        }

        void set_left_side(std::vector<BasicTerm> &&new_left_side) {
            assert(is_eq_or_ineq());
            params[0] = std::move(new_left_side);
        }

        void set_right_side(const std::vector<BasicTerm> &new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = new_right_side;
        }

        void set_right_side(std::vector<BasicTerm> &&new_right_side) {
            assert(is_eq_or_ineq());
            params[1] = std::move(new_right_side);
        }

        std::set<BasicTerm> get_set() const {
            std::set<BasicTerm> ret;
            for(const auto& side : this->params) {
                for(const BasicTerm& t : side)
                    ret.insert(t);
            }
            return ret;
        }

        std::set<BasicTerm> get_left_set() const {
            assert(is_eq_or_ineq());
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[0])
                ret.insert(t);
            return ret;
        }

        std::set<BasicTerm> get_right_set() const {
            assert(is_eq_or_ineq());
            std::set<BasicTerm> ret;
            for(const BasicTerm& t : this->params[1])
                ret.insert(t);
            return ret;
        }

        /**
         * @brief Get the length formula of the equation. For an equation X1 X2 X3 ... = Y1 Y2 Y3 ...
         * creates a formula |X1|+|X2|+|X3|+ ... = |Y1|+|Y2|+|Y3|+ ...
         *
         * @return LenNode Root of the length formula
         */
        LenNode get_formula_eq() const {

            auto plus_chain = [&](const std::vector<BasicTerm>& side) {
                std::vector<LenNode> ops;
                if(side.size() == 0) {
                    return LenNode(LenFormulaType::LEAF, BasicTerm(BasicTermType::Length, "0"), {});
                }
                if(side.size() == 1) {
                    return LenNode(LenFormulaType::LEAF, side[0], {});
                }
                for(const BasicTerm& t : side) {
                    LenNode n = LenNode(LenFormulaType::LEAF, t, {});
                    ops.push_back(n);
                }
                return LenNode(LenFormulaType::PLUS, ops);
            };

            LenNode left = plus_chain(this->params[0]);
            LenNode right = plus_chain(this->params[1]);
            LenNode eq = LenNode(LenFormulaType::EQ, {left, right});

            if(is_inequation()) {
                eq =  LenNode(LenFormulaType::NOT, {eq});
            }

            return eq;
        }

        std::vector<BasicTerm>& get_side(EquationSideType side);

        [[nodiscard]] const std::vector<BasicTerm>& get_side(EquationSideType side) const;

        [[nodiscard]] Predicate get_switched_sides_predicate() const {
            assert(is_eq_or_ineq());
            return Predicate{ type, { get_right_side(), get_left_side() } };
        }

        /**
         * @brief Replace BasicTerm @p find in the given concatenation
         *
         * @param concat Concatenation to be searche/replaced
         * @param find  Find
         * @param replace Replace
         * @param res Result
         * @return Does the concatenation contain at least one occurrence of @p find ?
         */
        static bool replace_concat(
                const std::vector<BasicTerm>& concat,
                const std::vector<BasicTerm>& find,
                const std::vector<BasicTerm>& replace,
                std::vector<BasicTerm>& res) {
            bool modif = false;
            for(auto it = concat.begin(); it != concat.end(); ) {
                if(std::equal(it, it+find.size(), find.begin(), find.end())) {
                    res.insert(res.end(), replace.begin(), replace.end());
                    modif = true;
                    it += find.size();
                } else {
                    res.push_back(*it);
                    it++;
                }
            }
            return modif;
        }

        /**
         * @brief Replace BasicTerm @p find in the predicate (do not modify the current one).
         *
         * @param find Find
         * @param replace Replace
         * @param res Where to store the modified predicate
         * @return Does the predicate contain at least one occurrence of @p find ?
         */
        bool replace(const std::vector<BasicTerm>& find, const std::vector<BasicTerm>& replace, Predicate& res) const {
            std::vector<std::vector<BasicTerm>> new_params;
            bool modif = false;
            for(const std::vector<BasicTerm>& p : this->params) {
                std::vector<BasicTerm> res_vec;
                bool r = Predicate::replace_concat(p, find, replace, res_vec);
                new_params.push_back(res_vec);
                modif = modif || r;
            }
            res = Predicate(this->type, new_params);
            return modif;
        }

        /**
         * Get unique variables on both sides of an (in)equation.
         * @return Variables in the (in)equation.
         */
        [[nodiscard]] std::set<BasicTerm> get_vars() const;

        /**
         * Get unique variables on a single @p side of an (in)equation.
         * @param[in] side (In)Equation side to get variables from.
         * @return Variables in the (in)equation on specified @p side.
         */
        [[nodiscard]] std::set<BasicTerm> get_side_vars(EquationSideType side) const;

        /**
         * Decide whether the @p side contains multiple occurrences of a single variable (with a same name).
         * @param side Side to check.
         * @return True if there are multiple occurrences of a single variable. False otherwise.
         */
        [[nodiscard]] bool mult_occurr_var_side(EquationSideType side) const;

        void replace(void* replace_map) {
            (void) replace_map;
            throw std::runtime_error("unimplemented");
        }

        void remove(void* terms_to_remove) {
            (void) terms_to_remove;
            throw std::runtime_error("unimplemented");
        }

        [[nodiscard]] bool equals(const Predicate& other) const;

        [[nodiscard]] std::string to_string() const;

        struct HashFunction {
            size_t operator()(const Predicate& predicate) const {
                size_t res{};
                size_t row_hash = std::hash<PredicateType>()(predicate.type);
                for (const auto& term: predicate.get_left_side()) {
                    size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                    res ^= col_hash;
                }
                for (const auto& term: predicate.get_right_side()) {
                    size_t col_hash = BasicTerm::HashFunction()(term) << 1;
                    res ^= col_hash;
                }
                return row_hash ^ res;
            }
        };

        // TODO: Additional operations.

    private:
        PredicateType type;
        std::vector<std::vector<BasicTerm>> params;

        // TODO: Add additional attributes such as cost, etc.
    }; // Class Predicate.

    [[nodiscard]] static std::string to_string(const Predicate& predicate) {
        return predicate.to_string();
    }

    static std::ostream& operator<<(std::ostream& os, const Predicate& predicate) {
        os << predicate.to_string();
        return os;
    }

    static bool operator==(const Predicate& lhs, const Predicate& rhs) { return lhs.equals(rhs); }
    static bool operator!=(const Predicate& lhs, const Predicate& rhs) { return !(lhs == rhs); }
    static bool operator<(const Predicate& lhs, const Predicate& rhs) {
        if (lhs.get_type() < rhs.get_type()) {
            return true;
        } else if (lhs.get_type() > rhs.get_type()) {
            return false;
        }
        // Types are equal. Compare data.
        if (lhs.get_params() < rhs.get_params()) {
            return true;
        }
        return false;
    }
    static bool operator>(const Predicate& lhs, const Predicate& rhs) { return !(lhs < rhs); }

    //----------------------------------------------------------------------------------------------------------------------------------

    class Formula {
    public:
        Formula(): predicates() {}

        std::vector<Predicate>& get_predicates() { return predicates; }
        const std::vector<Predicate>& get_predicates() const { return predicates; }

        // TODO: Use std::move for both add functions?
        void add_predicate(const Predicate& predicate) { predicates.push_back(predicate); }

        std::string to_string() const {
            std::string ret;
            for(const Predicate& p : this->predicates) {
                ret += p.to_string() + "\n";
            }
            return ret;
        }

        /**
         * @brief Get union of variables from all predicates
         *
         * @return std::set<BasicTerm> Variables
         */
        std::set<BasicTerm> get_vars() const {
            std::set<BasicTerm> ret;
            for(const auto& p : this->predicates) {
                auto vars = p.get_vars();
                ret.insert(vars.begin(), vars.end());
            }
            return ret;
        }

    private:
        std::vector<Predicate> predicates;
    }; // Class Formula.

} // Namespace smt::noodler.

namespace std {
    template<>
    struct hash<smt::noodler::Predicate> {
        inline size_t operator()(const smt::noodler::Predicate& predicate) const {
            size_t accum = smt::noodler::Predicate::HashFunction()(predicate);
            return accum;
        }
    };

    template<>
    struct hash<smt::noodler::BasicTerm> {
        inline size_t operator()(const smt::noodler::BasicTerm& basic_term) const {
            size_t accum = smt::noodler::BasicTerm::HashFunction()(basic_term);
            return accum;
        }
    };
}

#endif //Z3_NOODLER_FORMULA_H
