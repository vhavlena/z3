#include "memb_heuristics_procedures.h"

namespace smt::noodler {
    lbool MembHeuristicProcedure::compute_next_solution() {
        regex::RegexInfo reg_info = regex::get_regex_info(to_app(regex), m_util_s);
        if (is_regex_positive) {
            // x in RE is sat if and only if RE is not empty language
            if (reg_info.empty == l_false) {
                return l_true;
            } else if (reg_info.empty == l_true) {
                return l_false;
            }
        } else {
            // x not in RE is sat if and only if RE does not accept everything
            if (reg_info.universal == l_false) {
                return l_true;
            } else if (reg_info.universal == l_true) {
                return l_false;
            } else {
                // regex heuristic is not enough, so we try to create an automaton,
                // but we won't complement it, instead we will compare it with
                // the universal automaton (as complementation can blow up)

                // start with minterm representing symbols not ocurring in the regex
                std::set<mata::Symbol> symbols_in_regex{util::get_dummy_symbol()};
                regex::extract_symbols(regex, m_util_s, symbols_in_regex);
                regex::Alphabet reg_alph(symbols_in_regex);

                mata::nfa::Nfa nfa{ regex::conv_to_nfa(to_app(regex), m_util_s, reg_alph, false, false) };

                mata::EnumAlphabet alph(symbols_in_regex.begin(), symbols_in_regex.end());
                mata::nfa::Nfa sigma_star = mata::nfa::builder::create_sigma_star_nfa(&alph);

                if(mata::nfa::are_equivalent(nfa, sigma_star)) {
                    // x should not belong in sigma*, so it is unsat
                    // STRACE("str", tout << "Membership " << mk_pp(std::get<0>(reg_data), m) << " not in " << mk_pp(std::get<1>(reg_data), m) << " is unsat" << std::endl;);
                    return l_false;
                } else {
                    // otherwise x should not belong in some nfa that is not sigma*, so it is sat
                    reg_nfa = std::make_shared<mata::nfa::Nfa>(nfa);
                    return l_true;
                }
            }
        }
        return l_undef;
    }

    zstring MembHeuristicProcedure::get_model(BasicTerm var, std::function<rational(BasicTerm)> get_arith_model_of_var, std::function<rational(BasicTerm)> get_arith_model_of_length) {
        if (var != this->var) {
            util::throw_error("Cannot compute var that is not used in membership heuristic dec. proc.");
        }

        if (!reg_nfa) {
            // TODO: compute model from regex
            util::throw_error("Cannot compute model from regex directly");
        } else {
            SASSERT(!is_regex_positive);
            // TODO: get word that is NOT in reg_nfa (do not forget dummy symbol, use regex::Alphabet::get_string_from_mata_word)
            util::throw_error("Unsupported for now");
        }

        return zstring();
    }

    lbool MultMembHeuristicProcedure::compute_next_solution() {
        for (auto& [var, list_of_regexes] : var_to_list_of_regexes_and_complement_flag) {
            // sort the regexes using get_loop_sum, where those regexes that needs to be complemented should all be at the end
            std::sort(list_of_regexes.begin(), list_of_regexes.end(), [this](const std::pair<bool,app*>& l, const std::pair<bool,app*>& r) {
                return ((!l.first && r.first) | (regex::get_loop_sum(l.second, m_util_s) < regex::get_loop_sum(r.second, m_util_s)));
            });
            // STRACE("str-mult-memb-heur",
            //     tout << "Sorted regexes for var " << var << std::endl;
            //     unsigned i = 0;
            //     for (const auto & [is_complement, reg] : list_of_regexes) {
            //         tout << i << " (should " << (is_complement ? "" : "NOT ") <<"be complemented):" << mk_pp(reg, m) << std::endl;
            //     }
            // );

            std::vector<app*> list_of_normal_regs;
            std::vector<app*> list_of_compl_regs;
            for (auto& [is_complement, reg] : list_of_regexes) {
                if (is_complement) {
                    list_of_compl_regs.push_back(reg);
                } else {
                    list_of_normal_regs.push_back(reg);
                }
            }

            // Compute intersection L of all regexes that should not be complemented
            mata::nfa::Nfa intersection(1, {0}, {0});
            // initalize to universal automaton
            for (const mata::Symbol& symb : alph.get_alphabet()) {
                intersection.delta.add(0, symb, 0);
            }

            bool first = true;
            for (auto& reg : list_of_normal_regs) {
                intersection = mata::nfa::intersection(regex::conv_to_nfa(reg, m_util_s, alph, false, false), intersection);
                if (!first // for first iteration we won't do reduction, as it would just be done twice, once in conv_to_nfa and once here
                    && intersection.num_of_states() < regex::RED_BOUND)
                {
                    intersection = mata::nfa::reduce(intersection);
                }
                first = false;
                if (intersection.is_lang_empty()) {
                    STRACE("str-mult-memb-heur", tout << "intersection is empty => UNSAT" << std::endl;);
                    return l_false;
                }
            }

            // Compute union L' of all regexes that should be complemented (we are using de Morgan)
            mata::nfa::Nfa unionn; // initialize to empty automaton
            first = true;
            for (auto& reg : list_of_compl_regs) {
                unionn = mata::nfa::uni(regex::conv_to_nfa(reg, m_util_s, alph, false, false), unionn);
                if (!first // for first iteration we won't do reduction, as it would just be done twice, once in conv_to_nfa and once here
                    && unionn.num_of_states() < regex::RED_BOUND)
                {
                    unionn = mata::nfa::reduce(unionn);
                }
                first = false;
            }
            
            STRACE("str-mult-memb-heur", tout << "computing inclusion" << std::endl;);

            // We want to know if L \intersect \neg L' is empty, which is same as asking if L is subset of L'
            if (mata::nfa::is_included(intersection, unionn)) {
                // if inclusion holds, the intersection is empty => UNSAT
                STRACE("str-mult-memb-heur", tout << "inclusion holds => UNSAT" << std::endl;);
                return l_false;
            }

            
            if (!list_of_normal_regs.empty()) {
                intersections[var] = intersection;
            }

            if (!list_of_compl_regs.empty()) {
                unions[var] = unionn;
            }
        }

        STRACE("str-mult-memb-heur", tout << "inclusion holds for all vars => SAT" << std::endl;);
        return l_true;
    }
    
    zstring MultMembHeuristicProcedure::get_model(BasicTerm var, std::function<rational(BasicTerm)> get_arith_model_of_var, std::function<rational(BasicTerm)> get_arith_model_of_length) {
        STRACE("str-mult-memb-heur", tout << "getting model for " << var << std::endl;);
        if (unions.contains(var)) {
            // TODO: add support for getting some word from "intersections[var] \intersect \neg unions[var]" on the fly
            util::throw_error("Unsupported for now");
        }

        auto words = intersections.at(var).get_words(intersections.at(var).num_of_states());
        SASSERT(!words.empty());
        
        return alph.get_string_from_mata_word(*words.begin());
    }
}
