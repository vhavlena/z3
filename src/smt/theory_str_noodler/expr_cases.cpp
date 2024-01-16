#include <cassert>

#include "util/z3_exception.h"

#include "util.h"
#include "theory_str_noodler.h"
#include "inclusion_graph.h"
#include "aut_assignment.h"

namespace {
    using mata::nfa::Nfa;
}

namespace smt::noodler::expr_cases {

bool is_contains_index(expr* e, expr*& ind, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a) {
    // e.g. (str.contains (str.substr value2 0 (+ n (str.indexof value2 "A" 0))) "A")
    expr *subs = nullptr, *val = nullptr, *val_ind = nullptr, *str = nullptr, *str_ind = nullptr, *offset_ind = nullptr;
    if(m_util_s.str.is_contains(e, subs, val)) {     // subs = (str.substr value2 0 (+ n (str.indexof value2 "A" 0)))
        expr *subb1 = nullptr, *subb2 = nullptr, *num = nullptr;
        rational num_val; //n
        if(m_util_s.str.is_extract(subs, str, subb1, subb2)) {
            if(m_util_a.is_zero(subb1) && m_util_a.is_add(subb2, num, ind) && m_util_a.is_numeral(num, num_val) && num_val.get_int32() > 0) { 
                if(m_util_s.str.is_index(ind, str_ind, val_ind) || (m_util_s.str.is_index(ind, str_ind, val_ind, offset_ind) && m_util_a.is_zero(offset_ind))) {
                    if(str->hash() != str_ind->hash() || val->hash() != val_ind->hash()) {
                        return false;
                    }
                    return true;
                }
            }
        }
    }
    return false;
}

bool is_replace_indexof(expr* rpl_str, expr* rpl_find, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& ind) {
    expr* sub_str = nullptr, *sub_start = nullptr, *sub_len = nullptr;

    if(m_util_s.str.is_extract(rpl_str, sub_str, sub_start, sub_len)) {
        expr*ind_str = nullptr, *ind_find = nullptr, *ind_start = nullptr, *add = nullptr;
        rational one(1);
        if(m_util_a.is_zero(sub_start) && m_util_a.is_add(sub_len, add, ind) && m_util_a.is_numeral(add, one) && m_util_s.str.is_index(ind, ind_str, ind_find, ind_start) && one.get_int32() == 1) {
            if(ind_find->hash() != rpl_find->hash() || sub_str->hash() != ind_str->hash() || !m_util_a.is_zero(ind_start)) {
                return false;
            }
            return true;
        }
    }
    return false;
} 

bool is_indexof_add(expr* e, expr* index_str, ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, expr*& val, expr*& ind_find) {
    expr * ind = nullptr, *ind_str = nullptr, *ind_start = nullptr;
    if(m_util_a.is_add(e, val, ind) && m_util_s.str.is_index(ind, ind_str, ind_find, ind_start)) {
        if(ind_str->hash() != index_str->hash()) {
            return false;
        }
        return true;
    }
    return false;
}


}