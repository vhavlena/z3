
#include "formula_preprocess.h"

namespace smt::noodler {

    FormulaVar::FormulaVar(const Formula& conj) : allpreds(), input_size(0) {
        const std::vector<Predicate>& preds = conj.get_predicates();
        for(size_t i = 0; i < preds.size(); i++) {
            if(this->allpreds.find(preds[i]) == this->allpreds.end()) {
                this->predicates[i] = preds[i];
                this->allpreds.insert(preds[i]);
                this->update_varmap(preds[i], i);
                this->max_index = i;
                this->input_size++;
            }
        }
    }

    /**
     * @brief Update the structure collecting information about variable occurrence. The structure contains variables as 
     * [var] = { (var;eq_index;position) } s.t. position is negative if it is on the left side (numbering from 1).
     * 
     * @param pred Equation whose variables should be stored
     * @param index Index of the given equation @p pred.
     */
    void FormulaVar::update_varmap(const Predicate& pred, size_t index) {
        assert(pred.is_equation());
        for(const VarNode& vr : get_var_positions(pred, index)) {
            VarMap::iterator iter = this->varmap.find(vr.term.get_name());
            if(iter != this->varmap.end()) {
                iter->second.insert(vr);
            } else {
                this->varmap[vr.term.get_name()] = std::set<VarNode>({vr});
            }
        }
    }

    /**
     * @brief Get VarNode (structure representing variable position in the equation) for each 
     * variable in the equation @p pred.
     * 
     * @param pred Equation
     * @param index Index of the equation @p pred
     * @param incl_lit Include positions of literals
     * @return std::set<VarNode> Set if VarNodes for each occurrence of a variable.
     */
    std::set<VarNode> FormulaVar::get_var_positions(const Predicate& pred, size_t index, bool incl_lit) const {
        assert(pred.is_equation());
        std::set<VarNode> ret;
        int mult = -1;
        for(const std::vector<BasicTerm>& side : pred.get_params()) {
            update_var_positions_side(side, ret, index, incl_lit, mult);
            mult *= -1;
        }

        return ret;
    }

    /**
     * @brief Update BasicTerm positions in the concatenation
     * 
     * @param side Concatenation of BasicTerms
     * @param[out] res Set of positions (VarNodes)
     * @param index Index of the equation the @p side belongs to
     * @param incl_lit Include literals or just take variables?
     * @param mult Multiplicative constant of each position (used to distinguish between left (negative positions) and right side of an equation).
     */
    void FormulaVar::update_var_positions_side(const std::vector<BasicTerm>& side, std::set<VarNode>& res, size_t index, bool incl_lit, int mult) const {
        for(size_t i = 0; i < side.size(); i++) {
            if(incl_lit || side[i].is_variable()) {
                VarNode new_item = {.term = side[i], .eq_index = index, .position = mult*int(i+1) };
                    res.insert(new_item);
                }
            }
    }

    /**
     * @brief String representation of FormulaVar.
     * 
     * @return String representation
     */
    std::string FormulaVar::to_string() const {
        std::string ret;
        for(const auto& item : this->predicates) {
            ret += std::to_string(item.first) + ": " + item.second.to_string() + "\n";
        }
        for(const auto& item : this->varmap) {
            std::string st;
            if(!item.second.empty()) {
                st = item.second.begin()->to_string();
                std::for_each(std::next(item.second.begin()), item.second.end(), [&st] (const VarNode& val) {
                    st.append(", ").append(val.to_string());
                });
            }
            ret += item.first + ": {" + st + "}\n";
        }
        return ret;
    }

    /**
     * @brief Do all given variables occur at most once in the formula?
     * 
     * @param items Set of variables to be checked.
     * @return true All variables have unique occurrence.
     */
    bool FormulaVar::single_occurr(const std::set<BasicTerm>& items) const {
        for(const BasicTerm& t : items) {
            assert(t.get_type() == BasicTermType::Variable);
            if(this->varmap.at(t.get_name()).size() > 1) {
                return false;
            }
        }
        return true;
    }

    /**
     * @brief Is the given predicate @p p regular? If so, set @p out to the form that 
     * a single variable is on the left side.
     * 
     * @param p predicate to be checked (works for equalities only).
     * @param[out] out Adjusted form of the predicate s.t. |L| = 1
     * @return Is regular?
     */
    bool FormulaVar::is_side_regular(const Predicate& p, Predicate& out) const {
        std::vector<BasicTerm> side;

        if(p.get_left_side().size() == 1 && single_occurr(p.get_side_vars(Predicate::EquationSideType::Right))) {
            out = p;
            return true;
        } else if (p.get_right_side().size() == 1 && single_occurr(p.get_side_vars(Predicate::EquationSideType::Left))) {
            out = p.get_switched_sides_predicate();
            return true;
        }

        return false;
    } 

    /**
     * @brief Get all regular predicates from the formula (regular predicates are defined in remove_regular) with 
     * an additional condition that all predicates are switched to the form X = X_1...X_n (the single variable is 
     * on the left).
     * 
     * @param[out] out Vector of predicates with the corresponding index in the map predicates.
     */
    void FormulaVar::get_side_regulars(std::vector<std::pair<size_t, Predicate>>& out) const {
        for(const auto& item : this->predicates) {
            Predicate regular;
            if(is_side_regular(item.second, regular))
                out.push_back({item.first, regular});
        }
    }

    /**
     * @brief Remove predicate from the formula. Updates the variable map (if the variable is no further present in 
     * the system, it is not removed, only the set of occurrences is set to {}).
     * 
     * @param index Index of the predicate to be removed.
     */
    void FormulaVar::remove_predicate(size_t index) {
        std::set<BasicTerm> vars = this->predicates[index].get_vars();

        const auto& filter = [&index](const VarNode& n) { return n.eq_index == index; };
        for(const BasicTerm& v : vars) {
            std::set<VarNode>& occurr = this->varmap[v.get_name()]; 
            remove_if(occurr, filter);
        }
        this->allpreds.erase(this->predicates[index]);
        this->predicates.erase(index);
    }

    /**
     * @brief Add predicate to the formula (with updating the variable map).
     * 
     * @param pred New predicate
     * @param index Index of the new predicate (if set to -1, first higher index than top is chosen)
     */
    void FormulaVar::add_predicate(const Predicate& pred, int index) {
        if(this->allpreds.find(pred) != this->allpreds.end()) 
            return;
        if(index == -1) {
            assert(this->predicates.find(index) == this->predicates.end()); // check if the position is free
            this->max_index++;
            index = int(this->max_index);
        } else {
            assert(index >= 0);
            this->max_index = std::max(this->max_index, size_t(index));
        }

        this->predicates[index] = pred;
        this->allpreds.insert(pred);
        update_varmap(pred, size_t(index));
    }

    /**
     * @brief Add a set of new predicates.
     * 
     * @param preds Set of new predicates to be added
     */
    void FormulaVar::add_predicates(const std::set<Predicate>& preds) {
        for(const Predicate& p : preds) {
            add_predicate(p);
        }
    } 

    /**
     * @brief Replace @p find in the formula (in all predicates).
     * 
     * @param find Find 
     * @param replace Replace
     */
    void FormulaVar::replace(const BasicTerm& find, const std::vector<BasicTerm>& replace) {
        std::vector<std::pair<size_t, Predicate>> replace_map;
        for(const auto& pr : this->predicates) {
            Predicate rpl;
            if(pr.second.replace(find, replace, rpl)) { // changed, result is stored in rpl
                replace_map.push_back({pr.first, rpl});
            }
        }
        for(const auto& pr : replace_map) {
            remove_predicate(pr.first);
            add_predicate(pr.second, pr.first);
        } 
    }

    /**
     * @brief Iteratively remove regular predicates. A regular predicate is of the form X = X_1 X_2 ... X_n where 
     * X_1 ... X_n does not occurr elsewhere in the system. Formally, L = R is regular if |L| = 1 and each variable 
     * from Vars(R) has a single occurrence in the system only. Regular predicates can be removed from the system 
     * provided A(X) = A(X) \cap A(X_1).A(X_2)...A(X_n) where A(X) is the automaton assigned to variable X.
     */
    void FormulaPreprocess::remove_regular() {
        std::vector<std::pair<size_t, Predicate>> regs;
        this->formula.get_side_regulars(regs);
        std::deque<std::pair<size_t, Predicate>> worklist(regs.begin(), regs.end());

        while(!worklist.empty()) {
            std::pair<size_t, Predicate> pr = worklist.front();
            worklist.pop_front();
    
            assert(pr.second.get_left_side().size() == 1);
            update_reg_constr(pr.second.get_left_side()[0], pr.second.get_right_side());
        
            std::set<BasicTerm> vars = pr.second.get_vars();
            this->formula.remove_predicate(pr.first);
            for(const BasicTerm& v : vars) {
                std::set<VarNode> occurrs = this->formula.get_var_occurr(v.get_name());
                if(occurrs.size() == 1) {
                    Predicate reg_pred;
                    if(this->formula.is_side_regular(this->formula.get_predicate(occurrs.begin()->eq_index), reg_pred)) {
                        worklist.push_back({occurrs.begin()->eq_index, reg_pred});
                    }
                }
            }
        }
    }

    /**
     * @brief Get symmetrical difference of occurrences of BasicTerms within two concatenations. For instance for X.Y.X and X.Y.W.Z 
     * it returns ({{X,3}}, {{W,3}, {Z,4}}). It includes both variables and literals.
     * 
     * @param cat1 First concatenation
     * @param cat2 Second concatenation
     * @return Symmetrical difference 
     */
    VarNodeSymDiff FormulaPreprocess::get_eq_sym_diff(const std::vector<BasicTerm>& cat1, const std::vector<BasicTerm>& cat2) const {
        std::set<VarNode> p1, p2;
        this->formula.update_var_positions_side(cat1, p1, 0, true); // include positions of literals, set equation index to 0
        this->formula.update_var_positions_side(cat2, p2, 0, true);
        return {set_difference(p1, p2), set_difference(p2, p1)};
    }

    /**
     * @brief Check whether symmetric difference of term occurrences is suitable for generating identities. The 
     * symmetric difference contains different BasicTerms that are on the different positions in the contatenations. If so, 
     * set @p new_pred with the new predicate that was generated from the difference.
     * 
     * @param diff Symmetric difference of two equivalent terms (concatenation) 
     * @param[out] new_pred Newly created identity
     * @return Is it suitable for gen identity (was some identity created?)
     */
    bool FormulaPreprocess::generate_identities_suit(const VarNodeSymDiff& diff, Predicate& new_pred) const {
        if(diff.first.size() == 1 && diff.second.size() == 1) {
            VarNode val1 = *diff.first.begin();
            VarNode val2 = *diff.second.begin();
            if(val1.position == val2.position) {
                new_pred = Predicate(PredicateType::Equation, 
                    std::vector<std::vector<BasicTerm>>({std::vector<BasicTerm>({val1.term}), 
                    std::vector<BasicTerm>({val2.term})}));
                return true;
            }
        } // TODO: allow to generate X = eps
        return false;
    }

    /**
     * @brief Generate indentities. It covers two cases (a) X1 X X2 = X1 Y X2 => X = Y 
     * (b) X1 X X2 = Z and Z = X1 Y X2 => X = Y. Where each term can be both literal and variable.
     */
    void FormulaPreprocess::generate_identities() {
        std::set<Predicate> new_preds;
        for(const auto& pr1 : this->formula.get_predicates()) {
            for(const auto& pr2 : this->formula.get_predicates()) {
                if(pr1.first > pr2.first) 
                    continue;

                VarNodeSymDiff diff;
                if(pr1.first == pr2.first) { // two equations are the same
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr1.second.get_right_side());
                // L1 = R1 and L2 = R2 and L1 = L2 => R1 = R2
                } else if(pr1.second.get_left_side() == pr2.second.get_left_side()) { 
                    diff = get_eq_sym_diff(pr1.second.get_right_side(), pr1.second.get_right_side());
                // L1 = R1 and L2 = R2 and L1 = R2 => R1 = L2
                } else if(pr1.second.get_left_side() == pr2.second.get_right_side()) { 
                    diff = get_eq_sym_diff(pr1.second.get_right_side(), pr1.second.get_left_side());
                // L1 = R1 and L2 = R2 and R1 = L2 => L2 = R1
                } else if(pr1.second.get_right_side() == pr2.second.get_left_side()) { 
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr1.second.get_right_side());
                // L1 = R1 and L2 = R2 and R1 = R2 => L1 = L2
                } else if(pr1.second.get_right_side() == pr2.second.get_right_side()) { 
                    diff = get_eq_sym_diff(pr1.second.get_left_side(), pr1.second.get_left_side());
                }

                Predicate new_pred;
                if(generate_identities_suit(diff, new_pred)) {
                    this->formula.add_predicate(new_pred);
                    new_preds.insert(new_pred);
                }
            }
        }
        this->formula.add_predicates(new_preds);
    }

} // Namespace smt::noodler.
