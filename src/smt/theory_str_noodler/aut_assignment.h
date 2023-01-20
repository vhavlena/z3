
#ifndef Z3_STR_AUT_ASSIGNMENT_H_
#define Z3_STR_AUT_ASSIGNMENT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>

#include "inclusion_graph.h"
#include <mata/nfa.hh>

namespace smt::noodler {

    class AutAssignment : public std::unordered_map<BasicTerm, std::shared_ptr<Mata::Nfa::Nfa>> {

    public:

        // AutAssignment(std::unordered_map<BasicTerm, Mata::Nfa::Nfa> val): 
        //     std::unordered_map<BasicTerm, Mata::Nfa::Nfa>(val) { };

        // TODO this should probably be function of mata library
        Mata::Nfa::Nfa eps_automaton() const {
            Mata::Nfa::Nfa nfa(1);
            nfa.initial.add(0);
            nfa.final.add(0);
            return nfa;
        }

        Mata::Nfa::Nfa get_automaton_concat(const std::vector<BasicTerm>& concat) const {
            Mata::Nfa::Nfa ret = eps_automaton();
            for(const BasicTerm& t : concat) {
                ret = Mata::Nfa::concatenate(ret, *(this->at(t)));  // fails when not found
            }
            return ret;
        }

        bool is_epsilon(const BasicTerm &t) const {
            Mata::Nfa::Nfa v = Mata::Nfa::minimize(Mata::Nfa::remove_epsilon(*(this->at(t)))); // if we are sure that we have epsilon-free automata, we can skip remove_epsilon
            return v.get_num_of_trans() == 0 && v.initial.size() == 1 && v.final.size();
        }

        // adds all mappings of variables from other to this assigment except those which already exists in this assignment
        // i.e. if this[var] exists, then nothing happens for var, if it does not, then this[var] = other[var]
        // TODO: probably this is the same as just doing this->insert(other.begin(), other.end())
        // TODO: or even better, if we do not care what happens with other, we can use this->merge(other)
        void add_to_assignment(const AutAssignment &other) {
            for (const auto &it : other) {
                if (this->count(it.first) == 0) {
                    (*this)[it.first] = it.second;
                }
            }
        }

    };
        
} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
