
#ifndef _STATE_LEN_H_
#define _STATE_LEN_H_

#include <functional>
#include <list>
#include <set>
#include <stack>
#include <map>
#include <memory>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <smt/params/smt_params.h>
#include "ast/arith_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "smt/params/theory_str_params.h"
#include "smt/smt_kernel.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "util/scoped_vector.h"
#include "util/union_find.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/th_rewriter.h"

#include "util.h"

namespace smt::noodler {

    using Instance = obj_hashtable<expr>; // this likely needs to be refined
    using LengthConstr = expr_ref;  // this likely needs to be refined

    template<typename T>
    bool obj_hashtable_equal(const obj_hashtable<T>& ht1, const obj_hashtable<T>& ht2) {
        if(ht1.size() != ht2.size()) {
            return false;
        }
        for(T* const val : ht1) {
            if(!ht2.contains(val))
                return false;
        } 
        return true;
    } 

    /**
     * @brief Class representing the map Set(expr) -> T. Used for storing sets of processed 
     * conjunctions of string atoms. It can be used for storing the current state of computation 
     * for a given instance (set of string atoms). 
     * 
     * @tparam T Type of values for storing along with an instance
     */
    template<typename T>
    class StateLen {
    private:
        vector<std::pair<obj_hashtable<expr>, T>> state_visited;

    public:
        StateLen() : state_visited() { }

        bool contains(const obj_hashtable<expr>& state) {
            for(const auto& st : this->state_visited) {
                if(obj_hashtable_equal(st.first, state))
                    return true;
            }            
            return false;
        }

        void add(const obj_hashtable<expr>& state, const T& def) {
            if(!contains(state)){
                this->state_visited.push_back({state, def});
            }
        }

        const T& get_val(const Instance& inst) const {
            for(const auto& st : this->state_visited) {
                if(obj_hashtable_equal(st.first, inst))
                    return st.second;
            }            
            UNREACHABLE();
        }

        void update_val(const Instance& inst, const T& val) {
            for(auto& st : this->state_visited) {
                if(obj_hashtable_equal(st.first, inst)) {
                    st.second = val;   
                    return;
                }
            } 
        }
    };

    /**
     * @brief Debug instance of the Decision procedure. Always says SAT and return some length 
     * constraints. Simulates the situation when each instance has exactly 10 noodles.
     */
    class DecisionProcedureDebug {
    private:
        StateLen<int> state;
        ast_manager& m;
        seq_util& m_util_s;
        arith_util& m_util_a;

    public:
        DecisionProcedureDebug(ast_manager& mn, seq_util& util_s, arith_util& util_a) : 
            state(), 
            m(mn), 
            m_util_s(util_s), 
            m_util_a(util_a) 
            { }

        void initialize(const Instance& inst) {
            this->state.add(inst, 0);
        }

        bool get_another_solution(const Instance& inst, LengthConstr& out) {
            int cnt = this->state.get_val(inst);
            if(cnt >= 10) {
                return false;
            }

            expr_ref refinement_len(m);
            app* atom;
            for (const auto& eq : inst) {
                obj_hashtable<expr> vars;
                util::get_variables(to_app(eq), this->m_util_s, this->m, vars);

                for(expr * const var : vars) {
                    expr_ref len_str_l(m_util_s.str.mk_length(var), m);
                    SASSERT(len_str_l);
                    expr_ref num(m);
                    num = this->m_util_a.mk_numeral(rational(cnt), true);
                    atom = this->m_util_a.mk_le(len_str_l, num);
                    refinement_len = refinement_len == nullptr ? atom : m.mk_and(refinement_len, atom);
                }
            }

            this->state.update_val(inst, cnt+1);
            out = refinement_len;
            return true;
        }

        ~DecisionProcedureDebug() { }
    
    };
}

#endif