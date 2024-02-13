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

    /**
     * @brief Path with self-loops in the transition graph. 
     * Represents part of a transition graph.
     * 
     * @tparam Label Label type
     */
    template<typename Label>
    struct Path {
        std::vector<Formula> nodes;
        std::vector<Label> labels;
        std::map<Formula, Label> self_loops;

        /**
         * @brief Append path @p path to the current path.
         * 
         * @param path 
         */
        void append(const Path& path) {
            /// we assume that the path ends with the same node as it begins in @p path
            nodes.insert(nodes.end(), path.nodes.begin() + 1, path.nodes.end());
            labels.insert(labels.end(), path.labels.begin(), path.labels.end());
            self_loops.insert(path.self_loops.begin(), path.self_loops.end());
        }
    };

    /**
     * @brief Nielsen proof graph
     */
    template<typename Label>
    class TransitionGraph {
    public:
        using Nodes = std::set<Formula>;
        using Edges = std::map<Formula, std::set<std::pair<Formula, Label>>>;
    
        Nodes nodes;
        Edges edges;
        Formula init;
        std::set<Formula> fins {}; // zero or more final nodes

    public:

        const Nodes& get_nodes() const { return nodes; }

        void add_edge(const Formula& source, const Formula& target, const Label& lbl) {
            this->nodes.insert(source);
            this->nodes.insert(target);
            this->edges[source].emplace(target, lbl);
        }

        const Edges& get_edges() {
            return this->edges;
        }

        void set_init(const Formula& in) {
            this->init = in;
        }

        const Formula& get_init() const {
            return this->init;
        }

        void add_fin(const Formula& fin) {
            this->fins.insert(fin);
        }

        const std::set<Formula>& get_fins() const {
            return this->fins;
        }

        /**
         * @brief Convert graph to graphwiz.
         * 
         * @param lab_print Function for printing a label
         * @return std::string Transition graph in graphwiz
         */
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
            // there is at most one final
            if(this->fins.size() != 0) {
                ret.set_init(*this->fins.begin());
            }
            ret.fins = {this->init};

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
            for(const Formula& fin : this->get_fins()) {
                ret.add_fin(fin);
            }
            
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

        /**
         * @brief Get shortest path from @p start to @p end.
         * 
         * @param start First node
         * @param end Second node
         * @return std::optional<Path<Label>> Visited nodes and labels on the shortest path.
         */
        std::optional<Path<Label>> shortest_path(const Formula& start, const Formula& end) const {
            std::set<Formula> visited;
            std::deque<std::pair<Formula, Path<Label>>> worklist;
            worklist.emplace_back(std::pair<Formula, Path<Label>>(start, {{start},{}}));

            while(!worklist.empty()) {
                auto elem = worklist.front();
                worklist.pop_front();
                if(visited.find(elem.first) != visited.end()) {
                    continue;
                }
                visited.insert(elem.first);
                if(elem.first == end) {
                    return elem.second;
                }

                auto it = this->edges.find(elem.first);
                if(it == this->edges.end()) continue;
                for(const auto& tgt_symb : it->second) {
                    if(visited.find(tgt_symb.first) == visited.end()) {
                        std::vector<Label> path(elem.second.labels.begin(), elem.second.labels.end());
                        path.push_back(tgt_symb.second);
                        std::vector<Formula> nodes(elem.second.nodes.begin(), elem.second.nodes.end());
                        nodes.push_back(tgt_symb.first);
                        worklist.emplace_back(std::pair<Formula, Path<Label>>(tgt_symb.first, {nodes, path}));
                    }
                }
            }

            return std::nullopt;
        }
    };

    /**
     * @brief Transition label for a counter system. In the form of left := sum[0] + sum[1] + ...
     */
    struct CounterLabel {
        BasicTerm left;
        std::vector<BasicTerm> sum;
    };

    inline bool operator<(const CounterLabel& lhs, const CounterLabel& rhs) {
        if(lhs.left < rhs.left) {
            return true;
        } else if(lhs.left == rhs.left) {
            return lhs.sum < rhs.sum;
        }
        return false;
    }

    using NielsenLabel = std::pair<BasicTerm, Concat>;
    using NielsenGraph = TransitionGraph<NielsenLabel>;
    using CounterSystem = TransitionGraph<CounterLabel>;

    template<typename Label>
    using SelfLoop = typename std::pair<Formula, Label>;

    /**
     * @brief Decision procedure for quadratic equations using the Nielsen transformation.
     * 
     */
    class NielsenDecisionProcedure : public AbstractDecisionProcedure {
    private:
        std::unordered_set<BasicTerm> init_length_sensitive_vars;
        Formula formula;
        AutAssignment init_aut_ass;
        const theory_str_noodler_params& m_params;

        std::vector<NielsenGraph> graphs {};
        std::vector<std::vector<Path<CounterLabel>>> length_paths;
        size_t length_paths_index = 0;

        LenNode length_formula_for_solution = LenNode(LenFormulaType::TRUE);

    protected:
        // functions for the construction of a Nielsen graph
        bool is_pred_unsat(const Predicate& pred) const;
        bool is_pred_sat(const Predicate& pred) const {
            return pred.get_left_side().size() == 0 && pred.get_right_side().size() == 0;
        }
        std::set<NielsenLabel> get_rules_from_pred(const Predicate& pred) const;
        NielsenGraph generate_from_formula(const Formula& formula, bool early_termination, bool & is_sat) const;
        Formula trim_formula(const Formula& formula) const;
        std::vector<Formula> divide_independent_formula(const Formula& formula) const;

        /**
         * @brief Check if the predicate is length-unsatisfiable. It counts number of occurrences 
         * of each variable and sum of lengths of all predicates. Resolves based on this map.
         * 
         * @param pred Predicate to be checked
         * @return true -> unsatisfiable
         */
        static bool is_length_unsat(const Predicate& pred);

        /**
         * @brief Create a counter system from the Nielsen graph.
         * 
         * Returns false if the counter system cannot be created.
         * 
         * @param graph Graph to be converted to the counter system.
         * @param[out] result Created counter system
         */
        bool create_counter_system(const NielsenGraph& graph, CounterSystem& result) const;

        // counter graph condensation
        static void condensate_counter_system(CounterSystem& cs);
        static bool join_counter_label(const CounterLabel& l1, const CounterLabel& l2, CounterLabel & res);

        // extraction of a promising part of the condensated counter graph
        std::set<SelfLoop<CounterLabel>> find_self_loops(const CounterSystem& cs) const;
        bool get_length_path(const CounterSystem& cs, const SelfLoop<CounterLabel>& sl, Path<CounterLabel>& result);

        // construct length formula
        bool length_formula_path(const Path<CounterLabel>& path, std::map<BasicTerm, BasicTerm>& actual_var_map, std::vector<LenNode>& conjuncts);
        bool get_label_formula(const CounterLabel& lab, std::map<BasicTerm, BasicTerm>& in_vars, BasicTerm& out_var, std::vector<LenNode>& conjuncts);
        bool get_label_sl_formula(const CounterLabel& lab, const std::map<BasicTerm, BasicTerm>& in_vars, BasicTerm& out_var, std::vector<LenNode>& conjuncts);
        bool generate_len_connection(const std::map<BasicTerm, BasicTerm>& actual_var_map, std::vector<LenNode>& conjuncts);

    public:
        
        /**
         * Initialize a new decision procedure that can solve language (dis)equality constraints.
         * 
         * @param equalities encodes the language equations
         * @param init_aut_ass gives regular constraints (maps each variable from @p equalities to some NFA)
         * @param init_length_sensitive_vars the variables that occur in length constraints in the rest of formula
         * @param par Parameters for Noodler string theory.
         */
        NielsenDecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass,
                           const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                           const theory_str_noodler_params& par
         ) : init_length_sensitive_vars{ init_length_sensitive_vars },
             formula { equalities },
             init_aut_ass{ init_aut_ass },
             m_params(par) { 
            
            // Nielsen currently supports only equations (no inequalities and not(contains))
            if(!this->formula.all_of_type(PredicateType::Equation)) {
                util::throw_error("Nielsen supports quadratic equations only");
            }
        }

        lbool compute_next_solution() override;
        LenNode get_initial_lengths() override {
            return LenNode(LenFormulaType::TRUE);
        }
        std::pair<LenNode, LenNodePrecision> get_lengths() override;
        void init_computation() override;

        lbool preprocess(PreprocessType opt = PreprocessType::PLAIN, const BasicTermEqiv &len_eq_vars = {}) override;

    };

    static std::string nielsen_label_to_string(const NielsenLabel& lab) {
        std::string ret;
        ret += lab.first.to_string() + " ↦";
        ret += concat_to_string_compact(lab.second);
        return ret;
    }

    static std::string counter_label_to_string(const CounterLabel& lab) {
        std::string ret, sum;
        ret += lab.left.to_string() + " := ";

        for(const BasicTerm& bt : lab.sum) {
            sum += bt.get_name().encode() + "+";
        }
        if(sum.size() > 0) {
            sum.pop_back();
        }

        return ret + sum;
    }
}

#endif
