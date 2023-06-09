#ifndef _NOODLER_NIELSEN_DECISION_PROCEDURE_H_
#define _NOODLER_NIELSEN_DECISION_PROCEDURE_H_

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
     * @brief Nielsen proof graph
     */
    template<typename Label>
    class TransitionGraph {
    public:
        using Nodes = std::set<Formula>;
        // using Label = std::pair<BasicTerm, Concat>;
        using Edges = std::map<Formula, std::set<std::pair<Formula, Label>>>;
    private:
        Nodes nodes;
        Edges edges;
        Formula init;
        std::set<Formula> fins {}; // zero or more final nodes

    public:

        const Nodes& get_nodes() const { return nodes; }

        void add_edge(const Formula& source, const Formula& target, const Label& lbl) {
            this->nodes.insert(source);
            this->nodes.insert(target);
            this->edges[source].insert({target, lbl});
        }

        void set_init(const Formula& in) {
            this->init = in;
        }

        void add_fin(const Formula& fin) {
            this->fins.insert(fin);
        }

        std::string to_graphwiz(const std::function<std::string(const Label&)>& lab_print) const {
            std::string ret = "digraph nielsen_graph {\nrankdir=LR;\nnode [shape=\"rectangle\" style=\"rounded\" color=\"#cc4b3d\"]\n\"" + formula_to_string_compact(this->init) + "\"\nnode [shape=\"rectangle\" style=\"rounded\" color=black]\n";
            for(const auto& pr : this->edges) {
                for(const auto& lab_st : pr.second) {
                    ret += "\"" + formula_to_string_compact(pr.first) + "\" -> \"" + formula_to_string_compact(lab_st.first) + 
                        "\" [label=\"" + lab_print(lab_st.second) + "\"];\n";
                }
            }
            ret += "}";
            return ret;
        }

        /**
         * @brief Reverse direction of edges in the Nielsen graph.
         * 
         * @return NielsenGraph Graph with the reversed edges.
         */
        TransitionGraph reverse() const {
            TransitionGraph ret;
            ret.set_init(this->init);

            for(const auto& pr: this->edges) {
                for(const auto& tgt_symb : pr.second) {
                    ret.add_edge(tgt_symb.first, pr.first, tgt_symb.second);
                }
            }
            return ret;
        }

        /**
         * @brief Remove redundant nodes (that cannot reach a final node)
         * 
         * @return NielsenGraph Nielsen graph without redundant nodes
         */
        TransitionGraph trim() const {
            TransitionGraph rev = this->reverse();
            TransitionGraph ret;
            std::set<Formula> generated;
            std::deque<Formula> worklist(this->fins.begin(), this->fins.end());
            ret.set_init(this->init);
            
            while(!worklist.empty()) {
                Formula nd = worklist.front();
                generated.insert(nd);
                worklist.pop_front();

                for(const auto& tgt_symb : rev.edges[nd]) {
                    ret.add_edge(tgt_symb.first, nd, tgt_symb.second);
                    if(generated.find(tgt_symb.first) == generated.end()) {
                        worklist.push_back(tgt_symb.first);
                    }
                }
            }

            return ret;

        }
    };

    using NielsenLabel = std::pair<BasicTerm, Concat>;
    using CounterLabel = std::pair<BasicTerm, LenNode>;
    using NielsenGraph = TransitionGraph<NielsenLabel>;
    using CounterSystem = TransitionGraph<CounterLabel>;

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
        FormulaPreprocess prep_handler;
        const theory_str_noodler_params& m_params;

        std::vector<NielsenGraph> graphs {};

        bool is_pred_unsat(const Predicate& pred) const;
        bool is_pred_sat(const Predicate& pred) const {
            return pred.get_left_side().size() == 0 && pred.get_right_side().size() == 0;
        }

        std::set<NielsenLabel> get_rules_from_pred(const Predicate& pred) const;
        NielsenGraph generate_from_formula(const Formula& formula, bool & is_sat) const;
        Formula trim_formula(const Formula& formula) const;

        std::vector<Formula> divide_independent_formula(const Formula& formula) const;

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


    static std::string concat_to_string_compact(const Concat& con) {
        std::string ret;
        for(const BasicTerm& t : con) {
            if(t.is_literal()) {
                ret += "\\\"" + t.get_name().encode() + "\\\" ";
            } else {
                ret += t.to_string() + " ";
            }
        }
        if(ret.size() > 0) {
            ret.pop_back();
        }
        return ret;
    }

    static std::string pred_to_string_compact(const Predicate& pred) {
        if(!pred.is_equation()) {
            util::throw_error("NielsenGraph: unsupported predicate type");
        }

        std::string ret;
        ret = concat_to_string_compact(pred.get_left_side()) + " = " + 
            concat_to_string_compact(pred.get_right_side());
        return ret;
    }

    static std::string formula_to_string_compact(const Formula& f) {
        std::string ret;
        for(const Predicate& pred : f.get_predicates()) {
            ret += pred_to_string_compact(pred) + " & ";
        }
        if(ret.size() > 0) {
            return ret.substr(0, ret.size() - 3);
        }
        return ret;
    }

    

    static std::string nielsen_label_to_string(const NielsenLabel& lab) {
        std::string ret;
        ret += lab.first.to_string() + " ↦";
        ret += concat_to_string_compact(lab.second);
        return ret;
    }
}

#endif
