#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "nielsen_decision_procedure.h"

namespace smt::noodler {


    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions (currently true)
     */
    expr_ref NielsenDecisionProcedure::get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) {
        expr_ref res(m.mk_true(), m);
        return res;
    }

    /**
     * @brief Initialize computation.
     */
    void NielsenDecisionProcedure::init_computation() {

    }

    /**
     * @brief Preprocessing.
     */
    void NielsenDecisionProcedure::preprocess(PreprocessType opt) {
        this->prep_handler = FormulaPreprocess(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        this->prep_handler.separate_eqs();

        // Refresh the instance
        this->init_aut_ass = this->prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = this->prep_handler.get_len_variables();
        this->formula = this->prep_handler.get_modified_formula();
        this->formula = this->formula.split_literals();
    }

    /**
     * @brief Compute next solution. Generate all Nielsen graphs and perform the satifiability checking.
     * 
     * @return True -> satisfiable
     */
    bool NielsenDecisionProcedure::compute_next_solution() {
        std::cout << this->formula.to_string() << std::endl;

        bool sat = true;
        if(this->graphs.size() == 0) {
            std::vector<Formula> instances = divide_independent_formula(this->formula);
            for(const Formula& fle : instances) {
                bool is_sat;
                NielsenGraph graph = generate_from_formula(fle, is_sat);
                graph = graph.trim();
                this->graphs.push_back(graph);
                sat = sat && is_sat;
                std::cout << "SAT: " << is_sat << std::endl;
                std::cout << graph.to_graphwiz(nielsen_label_to_string) << std::endl;

                CounterSystem counter_system = create_counter_system(graph);
                std::cout << counter_system.to_graphwiz(counter_label_to_string);

            }
            return sat;
        } else {
            // TODO: enumerate all length solutions; if there is no more, return false
            return true;
        }
    }

    /**
     * @brief Divide the formula into a sequence of independent subformulae. A predicate is independent if its variables 
     * are disjoint with the  variables of the remaining predicates. The sequence consists of singleton predicate or the 
     * formula with the remaining ones.
     * 
     * @param formula Formula to be divided
     * @return std::vector<Formula> Sequence of independent subformulae.
     */
    std::vector<Formula> NielsenDecisionProcedure::divide_independent_formula(const Formula& formula) const {
        std::vector<Formula> ret;
        auto preds = formula.get_predicates();
        std::vector<std::set<BasicTerm>> vars_map(preds.size());
        std::set<size_t> rem_ind;
        std::set<size_t> all_ind;

        for(size_t i = 0; i < preds.size(); i++) {
            vars_map[i] = preds[i].get_vars();
        }
        
        for(size_t i = 0; i < preds.size(); i++) {
            all_ind.insert(i);
            bool add = true;
            for(size_t j = 0; j < preds.size(); j++) {
                if(i == j) {
                    continue;
                }
                std::vector<BasicTerm> inter;
                std::set_intersection(vars_map[i].begin(), vars_map[i].end(), 
                    vars_map[j].begin(), vars_map[j].end(), std::back_inserter(inter));
                if(!inter.empty()) {
                    add = false;
                    break;
                }
            }
            if(add) {
                rem_ind.insert(i);
                Formula split;
                split.add_predicate(preds[i]);
                ret.push_back(split);
            }
        }

        Formula remaining;
        std::vector<size_t> diff;
        std::set_difference(all_ind.begin(), all_ind.end(), rem_ind.begin(), 
            rem_ind.end(), std::back_inserter(diff));
        for(size_t ind : diff) {
            remaining.add_predicate(preds[ind]);
        }
        if(diff.size() > 0) {
            ret.push_back(remaining);
        }

        return ret;
    }

    NielsenDecisionProcedure::NielsenDecisionProcedure(
             const Formula &equalities, AutAssignment init_aut_ass,
             const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
             ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
             const theory_str_noodler_params& par
     ) :  m{ m }, m_util_s{ m_util_s }, m_util_a{ m_util_a }, init_length_sensitive_vars{ init_length_sensitive_vars },
         formula { equalities },
         init_aut_ass{ init_aut_ass },
         prep_handler{ equalities, init_aut_ass, init_length_sensitive_vars, par },
         m_params(par) {
         }

    /**
     * @brief Get all possible applicable rewriting rules from a predicate
     * 
     * @param pred Equation
     * @return std::set<NielsenLabel> All possible Nielsen rewriting rules
     */
    std::set<NielsenLabel> NielsenDecisionProcedure::get_rules_from_pred(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();
        std::set<NielsenLabel> ret;

        if(left.size() > 0 && left[0].is_variable() && right.size() > 0) {
            ret.insert({left[0], Concat({right[0], left[0]})});
        }
        if(right.size() > 0 && right[0].is_variable() && left.size() > 0) {
            ret.insert({right[0], Concat({left[0], right[0]})});
        }
        if(left.size() > 0 && left[0].is_variable()) {
            ret.insert({left[0], Concat()});
        }
        if(right.size() > 0 && right[0].is_variable()) {
            ret.insert({right[0], Concat()});
        }

        return ret;
    }

    /**
     * @brief Generate Nielsen graph from a formula.
     * 
     * @param init Initial node (formula)
     * @param[out] is_sat Contains the Nielsen graph an accepting node?
     * @return NielsenGraph 
     */
    NielsenGraph NielsenDecisionProcedure::generate_from_formula(const Formula& init, bool & is_sat) const {
        NielsenGraph graph;
        std::set<Formula> generated;
        std::deque<std::pair<size_t, Formula>> worklist;
        worklist.push_back({0, trim_formula(init)}); 
        graph.set_init(init);

        is_sat = false;
        while(!worklist.empty()) {
            std::pair<size_t, Formula> pr = worklist.front();
            size_t index = pr.first;
            generated.insert(pr.second);
            worklist.pop_front();

            std::vector<Predicate> predicates = pr.second.get_predicates();
            if(is_pred_unsat(predicates[index])) {
                continue;
            }
            for(; index < predicates.size(); index++) {
                if(!is_pred_sat(predicates[index])) {
                    break;
                }
            }
            if(index >= predicates.size()) {
                is_sat = true;
                graph.add_fin(pr.second);
                continue;
            }

            std::set<NielsenLabel> rules = get_rules_from_pred(predicates[index]);
            for(const auto& label : rules) {
                Formula rpl = trim_formula(pr.second.replace(Concat({label.first}), label.second));
                graph.add_edge(pr.second, rpl, label);
                if(generated.find(rpl) == generated.end()) {
                    worklist.push_back({index, rpl});
                }
            }
        }

        return graph;
    }

    /**
     * @brief Trim formula. Trim each predicate in the formula. A predicate is trimmed 
     * if it does not contain the same BasicTerm at the beginning of sides.
     * 
     * @param formula Formula
     * @return Formula Trimmed formula
     */
    Formula NielsenDecisionProcedure::trim_formula(const Formula& formula) const {
        Formula ret;

        for(const Predicate& pred : formula.get_predicates()) {
            auto params = pred.get_params();
            size_t len = std::min(params[0].size(), params[1].size());
            size_t i = 0;
            for(; i < len; i++) {
                if(params[0][i] != params[1][i]) {
                    break;
                }
            }
            std::vector<Concat> sides({
                Concat(params[0].begin()+i, params[0].end()),
                Concat(params[1].begin()+i, params[1].end())
            });
            ret.add_predicate(Predicate(PredicateType::Equation, sides));
        }
        return ret;
    }

    /**
     * @brief Check if a predicate is trivially unsat.
     * 
     * @param pred Predicate
     * @return true -> unsat
     */
    bool NielsenDecisionProcedure::is_pred_unsat(const Predicate& pred) const {
        Concat left = pred.get_left_side();
        Concat right = pred.get_right_side();

        if(left.size() == 0 && right.size() > 0 && right[0].is_literal()) {
            return true;
        }
        if(right.size() == 0 && left.size() > 0 && left[0].is_literal()) {
            return true;
        }
        if(left.size() > 0 && right.size() > 0 && right[0].is_literal() && left[0].is_literal() && right[0] != left[0]) {
            return true;
        }
        return false;
    }

    /**
     * @brief Create a counter system from the Nielsen graph.
     * 
     * @param graph Graph to be converted to the counter system.
     * @return CounterSystem
     */
    CounterSystem NielsenDecisionProcedure::create_counter_system(const NielsenGraph& graph) const {
        CounterSystem ret;

        // conversion of a nielsen label to the counter label
        auto conv_fnc = [&](const NielsenLabel& lab) {
            if(lab.second.size() == 0) {
                return CounterLabel{lab.first, {BasicTerm(BasicTermType::Length, "0")}};
            } else if(lab.second.size() == 2 && lab.second[0].is_literal()) {
                return CounterLabel{lab.first, {lab.second[1], BasicTerm(BasicTermType::Length, "1")}};
            } else if(lab.second.size() == 2 && lab.second[0].is_variable()) {
                return CounterLabel{lab.first, {lab.second[1], lab.second[0]}};
            } else {
                util::throw_error("create_counter_system: unsupported label type");
            }
        };

        ret.set_init(graph.get_init());
        for(const Formula& fin : graph.get_fins()) {
            ret.add_fin(fin);
        }
        for(const auto& pr : graph.edges) {
            for(const auto& trans : pr.second) {
                ret.add_edge(pr.first, trans.first, conv_fnc(trans.second));
            }
        }
        return ret;
    }

} // Namespace smt::noodler.
