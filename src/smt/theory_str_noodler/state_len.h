
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
}

#endif