
#include "formula_preprocess.h"

namespace smt::noodler {

    FormulaVar::FormulaVar(const Formula& conj) {
        const std::vector<Predicate>& preds = conj.get_predicates();
        this->input_size = preds.size();

        for(size_t i = 0; i < preds.size(); i++) {
            this->predicates[i] = preds[i];
            this->update_varmap(preds[i], i);
        }
    }


    void FormulaVar::update_varmap(const Predicate& pred, size_t index) {
        assert(pred.is_equation());
        int mult = -1;
        for(const std::vector<BasicTerm>& side : pred.get_params()) {
            for(size_t i = 0; i < side.size(); i++) {
                if(side[i].is_variable()) {
                    VarMap::iterator iter = this->varmap.find(side[i].get_name());
                    VarNode new_item = {.var = side[i].get_name(), .eq_index = index, .position = mult*int(i) };

                    if(iter != this->varmap.end()) {
                        iter->second.insert(new_item);
                    } else {
                        this->varmap[side[i].get_name()] = std::set<VarNode>({new_item});
                    }
                }
            }
            mult *= -1;
        }
    }

    std::string FormulaVar::to_string() const {
        std::string ret;
        for(const auto& item : this->predicates) {
            ret += std::to_string(item.first) + ": " + item.second.to_string() + "\n";
        }
        for(const auto& item : this->varmap) {
            std::string st = item.second.begin()->to_string();
            std::for_each(std::next(item.second.begin()), item.second.end(), [&st] (const VarNode& val) {
                st.append(", ").append(val.to_string());
            });
            ret += item.first + ": {" + st + "}\n";
        }
        return ret;
    }



} // Namespace smt::noodler.
