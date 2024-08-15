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

        std::set<BasicTerm> depend_on_block_var {};

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
         * Expressing that the begin of var_name is directly after last. We need to convert |last| to |lit_conversion[last]| if last is literal. Otherwise |last| is interpreted as number of characters of the temporary literal name.
         * 
         * @param var_name Variable name
         * @param last Variable/Literal preceeding var_name
         * @param lit_conversion Literal conversion 
         * @return LenNode 
         */
        LenNode generate_begin(const zstring& var_name, const BasicTerm& last, const std::map<zstring, BasicTerm>& lit_conversion) const;

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

        std::vector<Concat> get_side_eqs() const { return this->_constr_eqs; }

        std::set<BasicTerm> get_dependencies() const { return this->depend_on_block_var; }
    };

    /**
     * @brief Structure for a representation of a block model. 
     * Block are equations of the form x = R_i. A model of these equations can be computed from 
     * a model of x @p solution. 
     */
    struct BlockModel {
        zstring solution; // model of the block variable
        std::set<BasicTerm> terms {}; // other terms occurring in the equational block.
    };

    class LengthProcModel {

    private:
        std::vector<BasicTerm> length_vars {};
        std::map<BasicTerm, zstring> model {};
        std::map<BasicTerm, BlockModel> block_models {};
        std::map<zstring, BasicTerm> lit_conversion {};
        SubstitutionMap subst_map {};
        AutAssignment aut_ass {};
        ConstraintPool block_pool;

    protected:
        zstring assign_aut_ass_var(const BasicTerm& var, const std::function<rational(BasicTerm)>& get_arith_model_of_var);

        zstring assign_subst_map_var(const BasicTerm& var, const std::function<rational(BasicTerm)>& get_arith_model_of_var);

    public:

        LengthProcModel() { LengthProcModel(ConstraintPool{}, {}, {}); };
        LengthProcModel(const ConstraintPool& block_pool, const SubstitutionMap& subst, const AutAssignment& aut_ass);

        void generate_block_models(const BasicTerm& block_var, BlockModel& block_model, const std::function<rational(BasicTerm)>& get_arith_model_of_var);

        void compute_model(const std::function<rational(BasicTerm)>& get_arith_model_of_var); 

        void assign_free_vars(const std::function<rational(BasicTerm)>& get_arith_model_of_var);

        void assign_subst_map_vars(const std::function<rational(BasicTerm)>& get_arith_model_of_var);

        bool is_initialized() const { return !this->model.empty(); }


        void add_len_var(const BasicTerm& var) {
            this->length_vars.push_back(var);
        }

        /**
         * @brief Get already computed assignment of variable @p bt.
         * 
         * @param bt Variable
         * @return zstring String assignment
         */
        zstring get_var_model(const BasicTerm& bt) { return this->model.at(bt); }

        /**
         * @brief Get length variables that are relevant for model of @p str_var in the current model generators.
         * In fact we overapproximate and for each variable @p str_var we return all variables occurring 
         * in the model generators.
         * 
         * @param str_var String variable
         * @return std::vector<BasicTerm> Relevant variables (including temporary int variables) 
         */
        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) { return this->length_vars; };

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

        LengthProcModel len_model;
        SubstitutionMap subst_map {};

    protected:
        /**
         * @brief Check whether the preprocessed formula can be solved using the length-based procedure. 
         * It checks and stores multiple occurrences of variables @p multi_vars (do not include the constrained variables).
         * It also checks if formula contains equations only. 
         * 
         * @param[out] multi_vars Variables with multiple occurrences 
         * @return lbool l_under <-> the formula is out of the fragment
         */
        lbool check_formula(std::set<BasicTerm>& multi_vars);
    
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
             m_params(par),
             len_model() { 
        }

        lbool compute_next_solution() override;

        LenNode get_initial_lengths(bool all_vars = false) override {
            return LenNode(LenFormulaType::TRUE);
        }
        std::pair<LenNode, LenNodePrecision> get_lengths() override;
        void init_computation() override { };

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

        static bool is_suitable(const Formula &form, const AutAssignment& init_aut_ass);

        const Formula& get_formula() const {
            return this->formula;
        } 

         /**
         * @brief Get string model based on integer constraints.
         * 
         * @param var Variable whose model is obtained.
         * @param get_arith_model_of_var LIA model.
         * @return zstring String model of @p var
         */
        zstring get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) override;

        /**
         * @brief Get length variables that are relevant for model of @p str_var. 
         * 
         * @param str_var String variable
         * @return std::vector<BasicTerm> Relevant variables (including temporary int variables) 
         */
        std::vector<BasicTerm> get_len_vars_for_model(const BasicTerm& str_var) override;
    };
}

#endif
