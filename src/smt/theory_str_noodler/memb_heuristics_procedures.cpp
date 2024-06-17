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
                std::set<mata::Symbol> symbols_in_regex{get_dummy_symbol()};
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

    zstring MembHeuristicProcedure::get_model(BasicTerm var) {
        if (var != this->var) {
            util::throw_error("Cannot compute var that is not used in membership heuristic dec. proc.");
        }

        if (!reg_nfa) {
            // TODO: compute model from regex
            util::throw_error("Cannot compute model from regex directly");
        } else {
            SASSERT(!is_regex_positive);
            // TODO: get word that is NOT in reg_nfa
            util::throw_error("Unsupported for now");
        }
    }
}
