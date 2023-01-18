
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

    public:

        AutAssignment(std::map<BasicTerm, Mata::Nfa::Nfa> val): 
            std::map<BasicTerm, Mata::Nfa::Nfa>(val) { };

        Mata::Nfa::Nfa eps_automaton() const {
            Mata::Nfa::Nfa nfa(1);
            nfa.initial = {0};
            nfa.final = {0};
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

    };
        
} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
