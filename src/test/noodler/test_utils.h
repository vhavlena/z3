#include <iostream>
#include <algorithm>

#include <catch2/catch_test_macros.hpp>
#include <mata/re2parser.hh>
#include <utility>

#include "smt/theory_str_noodler/decision_procedure.h"
#include "smt/theory_str_noodler/theory_str_noodler.h"
#include "ast/reg_decl_plugins.h"

#ifndef Z3_TEST_UTILS_H
#define Z3_TEST_UTILS_H

using namespace smt::noodler;

class TheoryStrNoodlerCUT : public theory_str_noodler {
public:
    TheoryStrNoodlerCUT(smt::context &ctx, ast_manager &m, const theory_str_params &params)
            : theory_str_noodler(ctx, m, params) {}

    using theory_str_noodler::m_util_s, theory_str_noodler::m, theory_str_noodler::m_util_a;
};

class DecisionProcedureCUT : public DecisionProcedure {
public:
    DecisionProcedureCUT(const Formula &equalities, AutAssignment init_aut_ass,
                         const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
                         ast_manager& m, seq_util& m_util_s, arith_util& m_util_a
    ) : DecisionProcedure(equalities, std::move(init_aut_ass), init_length_sensitive_vars, m, m_util_s, m_util_a) {}

    using DecisionProcedure::compute_next_solution;
    using DecisionProcedure::get_lengths;
    using DecisionProcedure::preprocess;
    using DecisionProcedure::solution;
    using DecisionProcedure::init_computation;
};

// variables have one char names
inline Predicate create_equality(std::string left_side, std::string right_side) {
    std::vector<BasicTerm> left_side_vars;
    for (char var_name : left_side) {
        left_side_vars.push_back(BasicTerm(BasicTermType::Variable, std::string(1, var_name)));
    }
    std::vector<BasicTerm> right_side_vars;
    for (char var_name : right_side) {
        right_side_vars.push_back(BasicTerm(BasicTermType::Variable, std::string(1, var_name)));
    }
    return Predicate(PredicateType::Equation, { left_side_vars, right_side_vars});
}


inline BasicTerm get_var(char var) {
    return BasicTerm(BasicTermType::Variable, std::string(1, var));
}

inline std::shared_ptr<Mata::Nfa::Nfa> regex_to_nfa(const std::string& regex) {
    Mata::Nfa::Nfa aut;
    Mata::RE2Parser::create_nfa(&aut, regex);
    return std::make_shared<Mata::Nfa::Nfa>(aut);
}

inline std::map<BasicTerm, expr_ref> create_var_map(const std::unordered_set<BasicTerm>& vars, ast_manager& m, seq_util& m_util_s) {
    std::map<BasicTerm, expr_ref> ret;

    for(const BasicTerm& v : vars) {
        expr_ref var(m_util_s.mk_skolem(symbol(v.get_name()), 0, nullptr, m_util_s.mk_string_sort()), m);
        ret.insert({v, var});
    }

    return ret;
}

#endif //Z3_TEST_UTILS_H
