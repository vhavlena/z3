#include "smt/theory_str_noodler/theory_str_noodler.h"

namespace smt::noodler {
    Formula theory_str_noodler::get_word_formula_from_relevant() {
        Formula instance;

        for (const auto &we: this->m_word_eq_todo_rel) {
            Predicate inst = this->conv_eq_pred(ctx.mk_eq_atom(we.first, we.second));
            instance.add_predicate(inst);
        }

        for (const auto& wd : this->m_word_diseq_todo_rel) {
            Predicate inst = this->conv_eq_pred(m.mk_not(ctx.mk_eq_atom(wd.first, wd.second)));
            instance.add_predicate(inst);
        }

        return instance;
    }

    std::set<uint32_t> theory_str_noodler::get_symbols_from_relevant() {
        std::set<uint32_t> symbols_in_formula{};

        for (const auto &word_equation: m_word_eq_todo_rel) {
            util::extract_symbols(word_equation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_equation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &word_disequation: m_word_diseq_todo_rel) {
            util::extract_symbols(word_disequation.first, m_util_s, m, symbols_in_formula);
            util::extract_symbols(word_disequation.second, m_util_s, m, symbols_in_formula);
        }

        for (const auto &membership: m_membership_todo_rel) {
            util::extract_symbols(std::get<1>(membership), m_util_s, m, symbols_in_formula);
        }

        /* Get number of dummy symbols needed for disequations and 'x not in RE' predicates.
         * We need some dummy symbols, to represent the symbols not occuring in predicates,
         * otherwise, we might return unsat even though the formula is sat. For example if
         * we had x != y and no other predicate, we would have no symbols and the formula
         * would be unsat. With one dummy symbol, it becomes sat.
         * We add new dummy symbols for each diseqation and 'x not in RE' predicate, as we
         * could be in situation where we have for example x != y, y != z, z != x, and
         * |x| = |y| = |z|. If we added only one dummy symbol, then this would be unsat,
         * but if we have three symbols, it becomes sat (which this formula is). We add
         * dummy symbols also for 'x not in RE' because they basically represent
         * disequations too (for example 'x not in "aaa"' and |x| = 3 should be sat, but
         * with only symbol "a" it becomes unsat).
         * 
         * FIXME: We can possibly create more dummy symbols than the size of alphabet
         * (from the string theory standard the size of the alphabet is 196607), but
         * it is an edge-case that probably cannot happen.
         */
        size_t number_of_dummy_symbs = this->m_word_diseq_todo_rel.size();
        for (const auto& membership : this->m_membership_todo_rel) {
            if(!std::get<2>(membership)){
                number_of_dummy_symbs++;
            }
        }
        // to be safe, we set the minimum number of dummy symbols as 3
        number_of_dummy_symbs = std::max(number_of_dummy_symbs, size_t(3));

        // add needed number of dummy symbols to symbols_in_formula
        util::get_dummy_symbols(number_of_dummy_symbs, symbols_in_formula);

        return symbols_in_formula;
    }
}