
#ifndef Z3_STR_AUT_ASSIGNMENT_H_
#define Z3_STR_AUT_ASSIGNMENT_H_

#include <iostream>
#include <map>
#include <set>
#include <queue>
#include <string>
#include <memory>

#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <mata/nfa/builder.hh>

#include "formula.h"

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

        // used for tests, do not use normally
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

        Mata::Nfa::Nfa sigma_eps_automaton() const {
            Mata::Nfa::Nfa nfa{};
            nfa.initial = {0};
            nfa.final = {0,1};
            for (const Mata::Symbol& symb : this->alphabet) {
                nfa.delta.add(0, symb, 1);
            }
            return nfa;
        }

        Mata::Nfa::Nfa get_automaton_concat(const std::vector<BasicTerm>& concat) const {
            Mata::Nfa::Nfa ret = Mata::Nfa::Builder::create_empty_string_nfa();
            for(const BasicTerm& t : concat) {
                ret = Mata::Nfa::concatenate(ret, *(this->at(t)));  // fails when not found
            }
            return ret;
        }

        /**
         * @brief Checks if the automaton for @p t is equal to language containing only empty word.
         */
        bool is_epsilon(const BasicTerm &t) const {
            return Mata::Strings::is_lang_eps(*(this->at(t)));
        }

        /**
         * @brief Checks if the automaton for @p t contains empty word in its language.
         */
        bool contains_epsilon(const BasicTerm &t) const {
            return Mata::Nfa::is_in_lang(*(this->at(t)), {{}, {}});
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
        bool is_co_finite(const BasicTerm& t, int& len) const {
            Mata::OnTheFlyAlphabet mata_alphabet{};
            for (const auto& symbol : this->alphabet) {
                mata_alphabet.add_new_symbol(std::to_string(symbol), symbol);
            }

            auto cmp = Mata::Nfa::minimize(Mata::Nfa::complement(*(*this).at(t), mata_alphabet));
            if(!Mata::Nfa::is_lang_empty(cmp))
                len = cmp.size() - 1;
            else 
                len = -1;
            return cmp.size() == cmp.get_num_of_trans() + 1;
        }

        /**
         * @brief Check if the automaton accepts only a single word. It is only underapproximation,
         * as is_singleton is false for the NFA p1 -a-> p2, q1 -a-> q2 where p1, q1 are initial and p2, q2 are final.
         * To get a precise information, the determinization+minimization might be necessary, which is often 
         * expensive. 
         * 
         * @param t Variable
         * @return True -> is surely singleton, False -> inconclusive
         */
        bool is_singleton(const BasicTerm& t) const {
            Mata::Nfa::Nfa aut = *this->at(t);
            aut.trim();
            return aut.size() == aut.get_num_of_trans() + 1 && aut.initial.size() == 1 && aut.final.size() == 1;
        }

        /**
         * @brief Check if the language of the basic term has a fixed length
         * 
         * @param t BasicTerm
         * @param n[out] fixed length
         * @return True->fixed length
         */
        bool fixed_length(const BasicTerm& t, int& n) const {
            auto lengths = Mata::Strings::get_word_lengths(*this->at(t));
            if(lengths.size() != 1) {
                return false;
            }
            auto pr = *lengths.begin();
            n = pr.first;
            return pr.second == 0;
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

        std::string print() {
            std::stringstream res;
            for (const auto &key_val : *this) {
                res << "Automaton for " << key_val.first.get_name() << ":" << std::endl;
                key_val.second->print_to_DOT(res);
            }
            return res.str();
        }

        /**
         * @brief Restrict language of the given basic term @p t by @p restr_nfa.  
         * 
         * @param t Basic term to be restricted
         * @param restr_nfa Language restriction represented by an NFA.
         */
        void restrict_lang(const BasicTerm& t, const Mata::Nfa::Nfa& restr_nfa) {
            (*this)[t] = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::intersection(restr_nfa, *this->at(t)));
        }

        /**
         * @brief Get the length formula representing all possible lengths of the automaton for @p var
         */
        LenNode get_lengths(const BasicTerm& var) const;

        /**
         * Create NFA accepting a word in Z3 zstring representation.
         * @param word Word to accept.
         * @return NFA.
         */
        static Mata::Nfa::Nfa create_word_nfa(const zstring& word);

    };

} // Namespace smt::noodler.

#endif //Z3_STR_AUT_ASSIGNMENT_H_
