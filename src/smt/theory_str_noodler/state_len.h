
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

namespace smt::noodler {

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

    class StateLen {
    private:
        vector<obj_hashtable<expr>> state_visited;

    public:
        StateLen() : state_visited() { }

        bool visited(const obj_hashtable<expr>& state) {
            for(const auto& st : this->state_visited) {
                if(obj_hashtable_equal(st, state))
                    return true;
            }            
            return false;
        }

        void add_visited(const obj_hashtable<expr>& state) {
            if(!visited(state)){
                this->state_visited.push_back(state);
            }
        }
    };
}

#endif