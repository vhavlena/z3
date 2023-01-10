
#ifndef Z3_STR_AUT_ASSIGNMENT_H_
#define Z3_STR_AUT_ASSIGNMENT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>

#include "inclusion_graph.h"
#include <mata/nfa.hh>

namespace smt::noodler {

    class AutAssignment : public std::map<BasicTerm, Mata::Nfa::Nfa> {

    private:
        /// Union of all alphabets of automata in the aut assignment
        std::set<Mata::Nfa::Symbol> alphabet;

        void update_alphabet() {
            this->alphabet.clear();
            for (const auto& pr : *this) {
                auto alph_symbols = pr.second.alphabet == nullptr ? Mata::Nfa::OnTheFlyAlphabet::from_nfas(pr.second).get_alphabet_symbols() : pr.second.alphabet->get_alphabet_symbols();
                this->alphabet.insert(alph_symbols.begin(), alph_symbols.end());
            }
        }

    public:
        AutAssignment(std::map<BasicTerm, Mata::Nfa::Nfa> val): 
            std::map<BasicTerm, Mata::Nfa::Nfa>(val) { 
            update_alphabet();
        };

        Mata::Nfa::Nfa eps_automaton() const {
            Mata::Nfa::Nfa nfa(1);
            nfa.initial = {0};
            nfa.final = {0};
            return nfa;
        }

        Mata::Nfa::Nfa sigma_star_automaton() const {
            Mata::Nfa::Nfa nfa(1);
            nfa.initial_states = {0};
            nfa.final_states = {0};
            for (const Mata::Nfa::Symbol& symb : this->alphabet) {
                nfa.add_trans(0, symb, 0);
            }
            return nfa;
        }

        Mata::Nfa::Nfa get_automaton_concat(const std::vector<BasicTerm>& concat) const {
            Mata::Nfa::Nfa ret = eps_automaton();
            for(const BasicTerm& t : concat) {
                ret = Mata::Nfa::concatenate(ret, this->at(t));  // fails when not found
            }
            return ret;
        }

        bool is_epsilon(const BasicTerm &t) const {
            Mata::Nfa::Nfa v = Mata::Nfa::minimize(Mata::Nfa::remove_epsilon(this->at(t))); // if we are sure that we have epsilon-free automata, we can skip remove_epsilon
            return v.get_num_of_trans() == 0 && v.initial.size() == 1 && v.final.size();
        }

        const std::set<Mata::Nfa::Symbol> get_alphabet(bool recompute=false) {
            if(recompute) update_alphabet();
            return this->alphabet;
        }

    };
        
} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
