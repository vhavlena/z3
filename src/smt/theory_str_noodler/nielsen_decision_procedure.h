#ifndef _NOODLER_NIELSEN_DECISION_PROCEDURE_H_
#define _NOODLER_NIELSEN_DECISION_PROCEDURE_H_

#include <memory>
#include <deque>
#include <algorithm>

#include "smt/params/theory_str_noodler_params.h"
#include "formula.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"
#include "state_len.h"
#include "formula_preprocess.h"
#include "decision_procedure.h"

namespace smt::noodler {

    /**
     * @brief Nielsen proof graph
     */
    class NielsenGraph {
    public:
        using Nodes = std::set<Formula>;
        using Label = std::pair<BasicTerm, Concat>;
        using Edges = std::map<Formula, std::set<std::pair<Formula, Label>>>;
    private:
        Nodes nodes;
        Edges edges;

    public:

        const Nodes& get_nodes() const { return nodes; }

        void add_edge(const Formula& source, const Formula& target, const Label& lbl) {
            this->nodes.insert(source);
            this->nodes.insert(target);
            this->edges[source].insert({target, lbl});
        }
    };

    /**
     * @brief Decision procedure for quadratic equations using the Nielsen transformation.
     * 
     */
    class NielsenDecisionProcedure : public AbstractDecisionProcedure {
    protected:

        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        bool is_pred_unsat(const Predicate& pred) const;
        bool is_pred_sat(const Predicate& pred) const {
            return pred.get_left_side().size() == 0 && pred.get_right_side().size() == 0;
        }

        std::set<NielsenGraph::Label> get_rules_from_pred(const Predicate& pred) const;
        NielsenGraph generate_from_formula(const Formula& formula) const;

    public:
        NielsenDecisionProcedure(ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, const theory_str_noodler_params& par);

        NielsenDecisionProcedure(ast_manager& m, seq_util& m_util_s, arith_util& m_util_a);
        
        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p equalities to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param m Z3 AST manager
         * @param m_util_s Z3 string manager
         * @param m_util_a Z3 arithmetic manager
         * @param par Parameters for Noodler string theory.
         */
        NielsenDecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
                           const theory_str_noodler_params& par
         );

        bool compute_next_solution() override;
        expr_ref get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) override;
        void init_computation() override;

        void preprocess(PreprocessType opt = PreprocessType::PLAIN) override;

    };
}

#endif
