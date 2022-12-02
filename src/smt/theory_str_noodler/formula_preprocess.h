
#ifndef Z3_STR_FORMULA_PREPROCESS_H_
#define Z3_STR_FORMULA_PREPROCESS_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>

#include "inclusion_graph_node.h"

namespace smt::noodler {

    typedef std::string Var;

    /**
     * @brief Representation of a variable in an equation. Var is the variable name, eq_index 
     * is the equation index, and position represents the position of the variable in the equation. 
     * Negative value means left side, positive right side. 
     */
    struct VarNode {
        std::string var;
        size_t eq_index;
        int position;

        VarNode(const VarNode& other) = default;
        VarNode(VarNode &&) = default;

        VarNode& operator=(const VarNode&) = default;

        std::string to_string() const {
            std::string ret;
            ret += "( " + var + ";" + std::to_string(eq_index) + ";" + std::to_string(position) + ")";
            return ret;
        };
    };

    inline bool operator<(const VarNode& lhs, const VarNode& rhs) {
        if(lhs.position == rhs.position) {
            if(lhs.eq_index == rhs.eq_index) {
                if(lhs.var == rhs.var) return false;
                return lhs.var < rhs.var;
            }
            return lhs.eq_index < rhs.eq_index;
        }
        return lhs.position < rhs.position;
    }

    using VarMap = std::map<std::string, std::set<VarNode>>;


    /**
     * @brief Class representing a formula with efficient handling of variable occurrences.
     */
    class FormulaVar {
    
    private:
        std::map<size_t, Predicate> predicates; // formula
        VarMap varmap; // mapping of a variable name to a set of its occurrences in the formula
        size_t input_size; // number of equations in the input formula

    protected:
        void update_varmap(const Predicate& pred, size_t index);

    public:

        FormulaVar(const Formula& conj);
        
        std::string to_string() const;

        const std::set<VarNode>& get_var_occurr(const std::string& var) { return this->varmap[var]; };
        const Predicate& get_predicate(size_t index) const { return this->predicates.at(index); };
        void get_side_regulars(std::vector<std::pair<size_t, Predicate>>& out) const;

        bool single_occurr(const std::set<BasicTerm>& items) const;
        bool is_side_regular(const Predicate& p, Predicate& out) const;
    
        void remove_predicate(size_t index);
    };


    /**
     * @brief Class for formula preprocessing.
     */
    class FormulaPreprocess {

    private:
        FormulaVar formula;

    protected:
        void update_reg_constr(const BasicTerm& var, std::vector<BasicTerm>& upd) { };

    public:
        FormulaPreprocess(const Formula& conj) : formula(conj) { };

        const FormulaVar& get_formula() const { return this->formula; };
        std::string to_string() const { return this->formula.to_string(); };

        void remove_regular();
    };

    /**
     * @brief Remove from the set @p st all items satisfying the predicate @p pred.
     * 
     * @tparam T Set type
     * @tparam P Predicate type
     * @param st Set
     * @param pred predicate
     */
    template<typename T, typename P>
    void remove_if(std::set<T>& st, P pred) {
        for(auto it{st.begin()}, end{st.end()}; it != st.end();) {
            if(pred(*it))
                it = st.erase(it);
            else
                it++;
        }
    }
    
} // Namespace smt::noodler.

#endif //Z3_STR_FORMULA_PREPROCESS_H_
