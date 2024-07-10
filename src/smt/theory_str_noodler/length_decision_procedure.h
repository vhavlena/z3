#ifndef _NOODLER_LENGTH_DECISION_PROCEDURE_H_
#define _NOODLER_LENGTH_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"

#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    /**
     * @brief Pool of variable constraints
     * 
     */
    class ConstraintPool : public std::map<BasicTerm, class VarConstraint> {
    private:
        std::map<zstring, BasicTerm> lit_conversion {};

    public:
        void add_to_pool(const Predicate& pred);

        const std::map<zstring, BasicTerm> get_lit_conversion() const {
            return this->lit_conversion;
        }

        static zstring generate_lit_alias(const BasicTerm& lit, std::map<zstring, BasicTerm>& lit_conversion) {
            zstring new_lit_name = util::mk_noodler_var_fresh("lit").get_name();
            // lit_conversion[new_lit_name] = lit;
            lit_conversion.emplace(std::make_pair(new_lit_name, lit));
            return new_lit_name;
        }
    };

    /**
     * @brief Type for storing batch of equations of the form 
     * x = y1 y2 ... 
     * x = z1 z2 ...
     * It represents constraints on the variable x (_name). We call it constraints on variable x.
     */
    class VarConstraint {
    private:
        zstring _name; // name of the constrained variable
        std::vector<Concat> _constr_eqs;	// All sides of equations on the opposite side of this variable
        std::vector<zstring> _lits; // Literals occuring explicitly and in contained variables
        std::vector<std::pair<zstring, zstring>> _alignments;   // All literals, that should be aligned
        lbool is_parsed;
        // variables occurring in the variable constraint
        std::set<BasicTerm> vars {};

        /**
         * @brief Check if @p side is of the form [_name]
         * 
         * @param side Concatenation
         * @return @p side == [_name] 
         */
        bool check_side(const Concat& side);

        /**
         * @brief Emplace concatenation to the var constraint
         * 
         * @param c Concatenation
         * @param lit_conversion Occurrences of literals (unique names for the same literals) 
         */
        void emplace(const Concat& c, std::map<zstring, BasicTerm>& lit_conversion);

        /**
         * @brief Generate LIA formula b_x(var_name) = b_x(last) + |last| if last is not undef otherwise b(t) = 0
         * Expressing that the begin of var_name is directly after last
         * 
         * @param var_name Variable name
         * @param last Variable/Literal preceeding var_name
         * @return LenNode 
         */
        LenNode generate_begin(const zstring& var_name, const BasicTerm& last) const;

        /**
         * @brief Generate the LIA formula b_x(lit) = b_from(lit) + b_x(from) where 
         * x is the current constrained variable _name
         * 
         * Corresponds to the case when x = ... y ... && y = ... lit ....
         * then b_x(lit) = b_y(lit) + b_x(y)
         * 
         * @param lit Literal
         * @param from Source constrained variable
         * @return LenNode Len formula
         */
        LenNode generate_begin(const zstring& lit, const zstring& from) const;

        /**
         * @brief Generate LIA formula of the form |x| = |y_1| + ... where 
         * x = _name and y_1 ... is in @p side_len
         * 
         * @param side_len Concatenation of variables
         * @return LenNode Length formula
         */
        LenNode generate_side_eq(const std::vector<LenNode>& side_len) const;

        /**
         * @brief Generate LIA formula aligning literals @p l1 and @p l2
         * 
         * @param l1 Literal 1
         * @param l2 Literal 1
         * @param conv Occurrences of literals (unique names for the same literals)  
         * @return LenNode 
         */
        LenNode align_literals(const zstring& l1, const zstring& l2, const std::map<zstring, BasicTerm>& conv) const;

         /**
         * @brief Compare first n characters of l1 with last n characters of l2 (e.g. l1=banana, l2=ababa, n=2 -> [ba]nana, aba[ba] -> true)
         * 
         * @return bool match of substrings
         */
        static bool zstr_comp(const zstring& l1_val, const zstring& l2_val, unsigned n);
    public:
        VarConstraint() : _name(), is_parsed(l_false) {};
        VarConstraint(zstring name) : _name(std::move(name)), is_parsed (l_false) {};

        /**
         * @brief Add predicate to the the var constraint. Do not check if a equation side matches 
         * the variable name _name.
         * 
         * @param pred Predicate Predicate to be added
         * @param[out] lit_conversion Occurrences of literals (unique names for the same literals) 
         */
        void add(const Predicate& pred, std::map<zstring, BasicTerm>& lit_conversion);
        std::string to_string() const;

        /**
         * @brief Get literals occurring in the variable constrain and transitively in all var constraints in 
         * the system containing the variable in a side of current var constraint.
         * 
         * @return const std::vector<zstring>& Literals
         */
        // !!! Must be called after parse !!!
        const std::vector<zstring>& get_lits() const;

        /**
         * @brief Get variables occurring inside the var constraint
         * 
         * @return const std::set<BasicTerm> Variables
         */
        const std::set<BasicTerm> get_vars() const {
            return this->vars;
        }


        // TODO: already generate here
        /**
         * @brief parse var constraint
         * 
         * @param pool all var constraints
         * @param conv conversions for literals
         * @return bool success
         */
        bool parse(ConstraintPool& pool);
        
        /**
         * @brief Get length constraints generated by the batch of equations contraining x.
         * 
         * @param pool Pool of constraints on variables.
         * @return LenNode Length constraints on the current variable constraint
         */
        LenNode get_lengths(const ConstraintPool& pool) const;

        /**
         * @brief Get LIA formula saying that literals matching the same variables do not share any part.
         * Assumes that the var constraints contain @p multi_var.
         * 
         * @param pool Pool of var constraints
         * @param multi_var Variable with multiple occurrences
         * @param source_var Variable whose var constraints contains also the variable @p multi_var
         * @return LenNode LIA formula
         */
        LenNode get_multi_var_lia(const ConstraintPool& pool, const BasicTerm& multi_var, const BasicTerm& source_var) const;
    };

    /**
     * @brief Length-based decision procedure.
     * 
     */
    class LengthDecisionProcedure : public AbstractDecisionProcedure {
    private:
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        // the length formula from preprocessing, get_lengths should create conjunct with it
        LenNode preprocessing_len_formula = LenNode(LenFormulaType::TRUE,{});
        std::vector<LenNode> computed_len_formula {};
        std::vector<LenNode> implicit_len_formula {};

        // pool of variable constraints
        ConstraintPool pool {};
    public:
        LenNodePrecision precision = LenNodePrecision::PRECISE;

        /**
         * @brief Create fresh name for the given literal @p lit. 
         * 
         * @param lit Literal
         * @param lit_conversion Mapping of fresh names to the original literals
         * @return zstring 
         */
        // static zstring generate_lit_alias(const BasicTerm& lit, std::map<zstring, BasicTerm>& lit_conversion);

        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p form to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         */
        LengthDecisionProcedure(const Formula &form, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           const theory_str_noodler_params& par
         ) : init_length_sensitive_vars{ init_length_sensitive_vars },
             formula { form },
             init_aut_ass{ init_aut_ass },
             m_params(par) { 
        }

        lbool compute_next_solution() override;

        LenNode get_initial_lengths(bool all_vars = false) override {
            return LenNode(LenFormulaType::TRUE);
        }
        std::pair<LenNode, LenNodePrecision> get_lengths() override;
        void init_computation() override;

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        static bool is_suitable(const Formula &form, const AutAssignment& init_aut_ass);

        const Formula& get_formula() const {
            return this->formula;
        } 
    };
}

#endif
