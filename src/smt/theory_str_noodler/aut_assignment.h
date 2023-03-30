
#ifndef Z3_STR_AUT_ASSIGNMENT_H_
#define Z3_STR_AUT_ASSIGNMENT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>

#include "formula.h"
#include <mata/nfa.hh>
#include <mata/nfa-strings.hh>

namespace smt::noodler {

    /**
     * hints for using AutAssignment:
     *   - use at() instead of [] operator for getting the value, use [] only for assigning
     *   - if you want to assign some NFA, use std::make_shared<Mata::Nfa::Nfa>(NFA)
     */
    class AutAssignment : public std::unordered_map<BasicTerm, std::shared_ptr<Mata::Nfa::Nfa>> {

    private:
        /// Union of all alphabets of automata in the aut assignment
        std::set<Mata::Symbol> alphabet;

        void update_alphabet() {
            this->alphabet.clear();
            for (const auto& pr : *this) {
                auto alph_symbols = pr.second->alphabet == nullptr ? Mata::Nfa::create_alphabet(*(pr.second)).get_alphabet_symbols() : pr.second->alphabet->get_alphabet_symbols();
                this->alphabet.insert(alph_symbols.begin(), alph_symbols.end());
            }
        }

    public:
        using std::unordered_map<BasicTerm, std::shared_ptr<Mata::Nfa::Nfa>>::unordered_map;

        AutAssignment(std::map<BasicTerm, Mata::Nfa::Nfa> val) {
            for (const auto &key_value : val) {
                this->operator[](key_value.first) = std::make_shared<Mata::Nfa::Nfa>(key_value.second);
            }
            update_alphabet();
        };

        Mata::Nfa::Nfa sigma_star_automaton() const {
            Mata::Nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {0};
            for (const Mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 0);
            }
            return nfa;
        }

        Mata::Nfa::Nfa sigma_automaton() const {
            Mata::Nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {1};
            for (const Mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 1);
            }
            return nfa;
        }

        Mata::Nfa::Nfa get_automaton_concat(const std::vector<BasicTerm>& concat) const {
            Mata::Nfa::Nfa ret = Mata::Nfa::create_empty_string_nfa();
            for(const BasicTerm& t : concat) {
                ret = Mata::Nfa::concatenate(ret, *(this->at(t)));  // fails when not found
            }
            return ret;
        }

        bool is_epsilon(const BasicTerm &t) const {
            return Mata::Strings::is_lang_eps(*(this->at(t)));
        }

        // adds all mappings of variables from other to this assignment except those which already exists in this assignment
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

        const std::set<Mata::Symbol> get_alphabet(bool recompute=false) {
            if(recompute) update_alphabet();
            return this->alphabet;
        }

        void set_alphabet(const std::set<uint32_t>& alphabet) {
            this->alphabet.clear();
            for (const auto& symbol : alphabet) {
                this->alphabet.insert(symbol);
            }
        }

        /**
         * @brief Is language complement of a singleton?
         * 
         * @param t Variable whose language to be checked
         * @param[out] len Length of the word missing in the language
         * @return true Is complement of a word
         */
        bool is_co_finite(const BasicTerm& t, int& len) {
            Mata::OnTheFlyAlphabet mata_alphabet{};
            for (const auto& symbol : this->alphabet) {
                mata_alphabet.add_new_symbol(std::to_string(symbol), symbol);
            }

            auto cmp = Mata::Nfa::minimize(Mata::Nfa::complement(*(*this)[t], mata_alphabet));
            len = cmp.size() - 1;
            return cmp.size() == cmp.get_num_of_trans() + 1;
        }

        /**
         * @brief Check if all automata in the map have non-empty language.
         *
         * @return true All have non-empty language
         * @return false There is at least one NFA with the empty language
         */
        bool is_sat() const {
            for (const auto& pr : *this) {
                if(Mata::Nfa::is_lang_empty(*pr.second))
                    return false;
            }
            return true;
        }

        /**
         * @brief Reduce all automata occurring in the map.
         */
        void reduce() {
             for (auto& pr : *this) {
                pr.second = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::reduce(*pr.second));
            }
        }

        /**
         * @brief Get all keys from the assignment
         * 
         * @return std::unordered_set<BasicTerm> Keys
         */
        std::unordered_set<BasicTerm> get_keys() const {
            std::unordered_set<BasicTerm> ret;
            for(const auto & pr : *this) {
                ret.insert(pr.first);
            }
            return ret;
        }

    };

} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
