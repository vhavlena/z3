
#ifndef Z3_STR_FORMULA_PREPROCESS_H_
#define Z3_STR_FORMULA_PREPROCESS_H_

// #include <utility>
// #include <vector>
// #include <stdexcept>
// #include <memory>
// #include <cassert>
// #include <unordered_map>
// #include <string>
// #include <string_view>
// #include <set>

#include <map>
#include <set>
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
     * @brief Preprocessing of a conjunction of equations. 
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


    };
    
} // Namespace smt::noodler.

#endif //Z3_STR_FORMULA_PREPROCESS_H_
