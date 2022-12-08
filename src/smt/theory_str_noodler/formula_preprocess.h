
#ifndef Z3_STR_FORMULA_PREPROCESS_H_
#define Z3_STR_FORMULA_PREPROCESS_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>

#include "util/trace.h"
#include "inclusion_graph_node.h"

namespace smt::noodler {

    typedef std::string Var;

    /**
     * @brief Representation of a variable in an equation. Var is the variable name, eq_index 
     * is the equation index, and position represents the position of the variable in the equation. 
     * Negative value means left side, positive right side. 
     */
    struct VarNode {
        BasicTerm term;
        size_t eq_index;
        int position;

        VarNode(const VarNode& other) = default;
        VarNode(VarNode &&) = default;

        VarNode& operator=(const VarNode&) = default;

        bool operator==(const VarNode& other) const {
            return term == other.term && eq_index == other.eq_index && position == other.position;
        }

        std::string to_string() const {
            std::string ret;
            ret += "( " + term.to_string() + ";" + std::to_string(eq_index) + ";" + std::to_string(position) + ")";
            return ret;
        };
    };

    inline bool operator<(const VarNode& lhs, const VarNode& rhs) {
        if(lhs.position == rhs.position) {
            if(lhs.eq_index == rhs.eq_index) {
                if(lhs.term == rhs.term) return false;
                return lhs.term < rhs.term;
            }
            return lhs.eq_index < rhs.eq_index;
        }
        return lhs.position < rhs.position;
    }

    using VarMap = std::map<std::string, std::set<VarNode>>;
    using VarNodeSymDiff = std::pair<std::set<VarNode>, std::set<VarNode>>;

    /**
     * @brief Class representing a formula with efficient handling of variable occurrences.
     */
    class FormulaVar {
    
    private:
        std::map<size_t, Predicate> predicates; // formula
        std::set<Predicate> allpreds; // all predicates in a set
        VarMap varmap; // mapping of a variable name to a set of its occurrences in the formula
        size_t input_size; // number of equations in the input formula
        size_t max_index; // maximum occupied index 

    protected:
        void update_varmap(const Predicate& pred, size_t index);

    public:

        FormulaVar(const Formula& conj);
        
        std::string to_string() const;

        const std::set<VarNode>& get_var_occurr(const std::string& var) { return this->varmap[var]; };
        const Predicate& get_predicate(size_t index) const { return this->predicates.at(index); };
        const std::map<size_t, Predicate>& get_predicates() const { return this->predicates; };
        const std::set<Predicate>& get_predicates_set() const { return this->allpreds; };
        const VarMap& get_varmap() const { return this->varmap; };
        void get_side_regulars(std::vector<std::pair<size_t, Predicate>>& out) const;
        void get_simple_eqs(std::vector<std::pair<size_t, Predicate>>& out) const;
        bool contains_simple_eqs() const { std::vector<std::pair<size_t, Predicate>> out; get_simple_eqs(out); return out.size() > 0;  }

        std::set<VarNode> get_var_positions(const Predicate& pred, size_t index, bool incl_lit=false) const;
        void update_var_positions_side(const std::vector<BasicTerm>& side, std::set<VarNode>& res, size_t index, bool incl_lit=false, int mult=1) const;

        bool single_occurr(const std::set<BasicTerm>& items) const;
        bool is_side_regular(const Predicate& p, Predicate& out) const;
        /**
         * @brief Is equation simple (equation of the form X=Y)
         * 
         * @param p Equation
         * @return Is simple?
         */
        bool is_simple_eq(const Predicate& p) const { assert(p.is_equation()); return p.get_left_side().size() == 1 && p.get_right_side().size() == 1; };
    
        void remove_predicate(size_t index);
        void add_predicate(const Predicate& pred, int index = -1);
        void add_predicates(const std::set<Predicate>& preds);

        void replace(const BasicTerm& find, const std::vector<BasicTerm>& replace);
        void clean_varmap();
    };


    /**
     * @brief Class for formula preprocessing.
     */
    class FormulaPreprocess {

    private:
        FormulaVar formula;

    protected:
        void update_reg_constr(const BasicTerm& var, std::vector<BasicTerm>& upd) {/** TODO */ };
        VarNodeSymDiff get_eq_sym_diff(const std::vector<BasicTerm>& cat1, const std::vector<BasicTerm>& cat2) const;
        bool generate_identities_suit(const VarNodeSymDiff& diff, Predicate& new_pred) const;

    public:
        FormulaPreprocess(const Formula& conj) : formula(conj) { };

        const FormulaVar& get_formula() const { return this->formula; };
        std::string to_string() const { return this->formula.to_string(); };

        void remove_regular();
        void propagate_variables();
        void generate_identities();

        void replace(const BasicTerm& find, const std::vector<BasicTerm>& replace) { this->formula.replace(find, replace); };
        void clean_varmap() { this->formula.clean_varmap(); };
    };

    /**
     * @brief Remove from the container @p st all items satisfying the predicate @p pred.
     * 
     * @tparam T Container type
     * @tparam P Predicate type
     * @param st Set
     * @param pred predicate
     */
    template<typename T, typename P>
    void remove_if(T& st, P pred) {
        for(auto it{st.begin()}, end{st.end()}; it != st.end();) {
            if(pred(*it))
                it = st.erase(it);
            else
                it++;
        }
    }

    /**
     * @brief Set difference
     * 
     * @tparam T type of sets
     * @param t1 First set
     * @param t2 Second set
     * @return @p t1 \ @p t2
     */
    template<typename T>
    std::set<T> set_difference(std::set<T>& t1, std::set<T>& t2) {
        std::set<T> diff;
        std::set_difference(t1.begin(), t1.end(), t2.begin(), t2.end(),
            std::inserter(diff, diff.begin()));
        return diff;
    }
    
} // Namespace smt::noodler.

#endif //Z3_STR_FORMULA_PREPROCESS_H_
