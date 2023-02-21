
#include "formula_preprocess.h"
#include <mata/nfa.hh>

namespace smt::noodler {

    FormulaVar::FormulaVar(const Formula& conj) : allpreds(), input_size(0) {
        const std::vector<Predicate>& preds = conj.get_predicates();
        for(size_t i = 0; i < preds.size(); i++) {
            // we skip equations of the form X = X
            if(preds[i].is_equation() && preds[i].get_left_side() == preds[i].get_right_side()) {
                continue;
            }
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
        for(const VarNode& vr : get_var_positions(pred, index, true)) {
            VarMap::iterator iter = this->varmap.find(vr.term);
            if(iter != this->varmap.end()) {
                iter->second.insert(vr);
            } else {
                this->varmap[vr.term] = std::set<VarNode>({vr});
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
            ret += item.first.to_string() + ": {" + st + "}\n";
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
            if(this->varmap.at(t).size() > 1) {
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

        if(!p.is_equation()) {
            return false;
        }

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
     * @brief Get simple equations. Simple equation is of the form X = Y where |X| = |Y| = 1.
     *
     * @param[out] out Vector of simple equations with the corresponding index in the map predicates
     */
    void FormulaVar::get_simple_eqs(std::vector<std::pair<size_t, Predicate>>& out) const {
        for(const auto& item : this->predicates) {
            if(is_simple_eq(item.second))
                out.push_back({item.first, item.second});
        }
    }

    /**
     * @brief Clean occurrences of variables that have empty set of occurrences from varmap.
     * In other words remove items from varmap s.t. (x, {}).
     */
    void FormulaVar::clean_varmap() {
        remove_if(this->varmap, [](const auto& n) { return n.second.size() == 0; });
    };

    /**
     * @brief Remove predicate from the formula. Updates the variable map (if the variable is no further present in
     * the system, it is not removed, only the set of occurrences is set to {}).
     *
     * @param index Index of the predicate to be removed.
     */
    void FormulaVar::remove_predicate(size_t index) {
        std::set<BasicTerm> items = this->predicates[index].get_set();

        const auto& filter = [&index](const VarNode& n) { return n.eq_index == index; };
        for(const BasicTerm& v : items) {
            std::set<VarNode>& occurr = this->varmap[v];
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
    int FormulaVar::add_predicate(const Predicate& pred, int index) {
        auto it = this->allpreds.find(pred);
        if(it != this->allpreds.end()) {
            for(const auto& pr : this->predicates) { // WARNING: ineffective; needs to iterate over all predicates
                if(pr.second == pred)
                    return pr.first;
            }
            assert(false);
        }
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
        return index;
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
    void FormulaVar::replace(const Concat& find, const Concat& replace) {
        std::vector<std::pair<size_t, Predicate>> replace_map;
        for(const auto& pr : this->predicates) {
            Predicate rpl;
            if(pr.second.replace(find, replace, rpl)) { // changed, result is stored in rpl
                assert(rpl != pr.second);
                replace_map.push_back({pr.first, std::move(rpl)});
            }
        }
        for(const auto& pr : replace_map) {
            remove_predicate(pr.first);
            add_predicate(pr.second, pr.first);
        }
    }

    /**
     * @brief Remove equations with both sides empty.
     */
    void FormulaVar::clean_predicates() {
        std::vector<size_t> rem_ids;
        for(const auto& pr : this->predicates) {
            if(!pr.second.is_equation())
                continue;
            if(pr.second.get_left_side().size() == 0 && pr.second.get_right_side().size() == 0)
                rem_ids.push_back(pr.first);
        }
        for(size_t id : rem_ids) {
            remove_predicate(id);
        }
    };

    /**
     * @brief Update automata assignment of @p var. If var exists in the aut assignment, we set
     * L(var) = L(var) \cap L(upd). Otherwise we set L(var) = L(upd).
     *
     * @param var Basic term to be updated
     * @param upd Concatenation of terms for updating @p var.
     */
    void FormulaPreprocess::update_reg_constr(const BasicTerm& var, const std::vector<BasicTerm>& upd) {
        Mata::Nfa::Nfa concat = this->aut_ass.get_automaton_concat(upd);
        auto iter = this->aut_ass.find(var);
        if(iter != this->aut_ass.end()) {
            Mata::Nfa::Nfa inters = Mata::Nfa::intersection(*(iter->second), concat);
            inters.trim();
            this->aut_ass[var] = std::make_shared<Mata::Nfa::Nfa>(inters);
        } else {
            this->aut_ass[var] = std::make_shared<Mata::Nfa::Nfa>(concat);
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

            // right side containts len variables; skip
            if(!set_disjoint(this->len_variables, pr.second.get_side_vars(Predicate::EquationSideType::Right))) {
                continue;
            }
            update_reg_constr(pr.second.get_left_side()[0], pr.second.get_right_side());

            std::set<BasicTerm> vars = pr.second.get_vars();
            this->formula.remove_predicate(pr.first);
            for(const BasicTerm& v : vars) {
                std::set<VarNode> occurrs = this->formula.get_var_occurr(v);
                if(occurrs.size() == 1) {
                    Predicate reg_pred;
                    if(this->formula.is_side_regular(this->formula.get_predicate(occurrs.begin()->eq_index), reg_pred)) {
                        worklist.emplace_back(occurrs.begin()->eq_index, reg_pred);
                        // update dependency
                        map_set_insert(this->dependency, occurrs.begin()->eq_index, pr.first);
                    }
                }
            }
        }
    }

    /**
     * @brief Propagate variables. Propagate all equations of the form X=Y
     * (find all Y in the formula and replace with X).
     */
    void FormulaPreprocess::propagate_variables() {
        std::vector<std::pair<size_t, Predicate>> regs;
        this->formula.get_simple_eqs(regs);
        std::deque<size_t> worklist;

        std::transform(regs.begin(), regs.end(), std::back_inserter(worklist),
            [](auto const& pair){ return pair.first; });

        while(!worklist.empty()) {
            size_t index = worklist.front();
            worklist.pop_front();
            Predicate eq = this->formula.get_predicate(index);
            if(eq.get_left_side() == eq.get_right_side()) {
                this->formula.remove_predicate(index);
                continue;
            }

            assert(eq.get_left_side().size() == 1 && eq.get_right_side().size() == 1);
            BasicTerm v_left = eq.get_left_side()[0]; // X
            update_reg_constr(v_left, eq.get_right_side()); // L(X) = L(X) cap L(Y)
            this->len_formulae.push_back(eq.get_formula_eq()); // add len constraint |X| = |Y|
            // propagate len variables: if Y is in len_variables, include also X
            if(this->len_variables.find(eq.get_right_side()[0]) != this->len_variables.end()) {
                this->len_variables.insert(v_left);
            }

            this->formula.replace(eq.get_right_side(), eq.get_left_side()); // find Y, replace for X
            this->formula.remove_predicate(index);

            // update dependencies (overapproximation). Each remaining predicat depends on the removed one.
            for(const auto& pr : this->formula.get_predicates()) {
                map_set_insert(this->dependency, pr.first, index);
            }

            STRACE("str", tout << "propagate_variables\n";);
        }

        assert(!this->formula.contains_simple_eqs());
    }

    /**
     * @brief Get symmetrical difference of occurrences of BasicTerms within two concatenations. For instance for X.Y.X and X.Y.W.Z
     * it returns ({{X,3}}, {{W,3}, {Z,4}}). It includes both variables and literals.
     *
     * @param cat1 First concatenation
     * @param cat2 Second concatenation
     * @return Symmetrical difference
     */
    VarNodeSymDiff FormulaPreprocess::get_eq_sym_diff(const Concat& cat1, const Concat& cat2) const {
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
                    std::vector<Concat>({Concat({val1.term}),
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
        std::set<std::pair<size_t, Predicate>> new_preds;
        size_t index = this->formula.get_max_index() + 1;

        for(const auto& pr1 : this->formula.get_predicates()) {
            if(!pr1.second.is_equation())
                continue;
            for(const auto& pr2 : this->formula.get_predicates()) {
                if(!pr2.second.is_equation())
                    continue;
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
                    new_preds.insert({index, new_pred});
                    this->dependency[index] = std::set<size_t>({pr1.first, pr2.first});
                    index++;
                }
            }
        }
        for(const auto &pr : new_preds) {
            this->formula.add_predicate(pr.second, pr.first);
        }
    }

    /**
     * @brief Create concatenation graph. Oriented graph where each term is node and two terms
     * (variable/litaral) t1 and t2 are connected (t1 -> t2) if t1.t2 occurs in some equation.
     * Moreover each edge is labelled by number of occurrences of such concatenation in the formula.
     *
     * @return ConcatGraph of the formula.
     */
    ConcatGraph FormulaPreprocess::get_concat_graph() const {
        ConcatGraph graph;

        for(const Predicate& pr : this->formula.get_predicates_set()) {
            for(const std::vector<BasicTerm>& side : pr.get_params()) {
                for(size_t i = 0; i <= side.size(); i++) {
                    // we use variable with empty name to denote that the variable varname is at the end of the side
                    BasicTerm from = graph.init();
                    BasicTerm to = graph.init();
                    if (i > 0) {
                        from = side[i-1];
                    }
                    if(i < side.size()) {
                        to = side[i];
                    }
                    graph.add_edge(from, to);
                }
            }
        }
        return graph;
    }

    /**
     * @brief Get regular sublists, i.e., concatenations X1...Xk such that each Xi occurrs (if it is a variable) in the
     * formula only in  X1...Xk. In other words, if we replace X1...Xk by a fresh variable V, then
     * X+ ... Xk do not occurr in the formula anymore (except in V).
     *
     * @param res Regular sublists with the number of their occurrences.
     */
    void FormulaPreprocess::get_regular_sublists(std::map<Concat, unsigned>& res) const {
        ConcatGraph graph = get_concat_graph();

        for(const BasicTerm& t : graph.get_init_vars()) {
            Concat sub;
            // Get all occurrences of t
            std::set<VarNode> occurrs = this->formula.get_var_occurr(t);
            // Get predicate of a first equation containing t; and side containing t
            Predicate act_pred = this->formula.get_predicate(occurrs.begin()->eq_index);
            Concat side = occurrs.begin()->position > 0 ? act_pred.get_right_side() : act_pred.get_left_side();

            int start = std::abs(occurrs.begin()->position) - 1;
            for(int i = start; i < side.size(); i++) {
                std::set<VarNode> vns;
                // Construct the set of supposed occurences of the symbol side[i]
                for(const VarNode& vn : occurrs) {
                    vns.insert({
                        .term = side[i],
                        .eq_index = vn.eq_index,
                        .position = FormulaVar::increment_side_index(vn.position, i-start)
                    });
                }
                // Compare the supposed occurrences with real occurrences.
                std::set<VarNode> occurs_act = this->formula.get_var_occurr(side[i]);

                // do not include length variables
                if(this->len_variables.find(side[i]) != this->len_variables.end()) {
                    break;
                }
                if(side[i].is_variable() && vns != occurs_act) {
                    break;
                }
                if(side[i].is_literal() && !std::includes(occurs_act.begin(),
                    occurs_act.end(), vns.begin(), vns.end())) {
                    break;
                }
                sub.push_back(side[i]);
            }

            if(sub.size() > 1) {
                res[sub] = occurrs.size();
            }
        }
    }

    /**
     * @brief Create a fresh variable.
     *
     * @return BasicTerm Corresponding to a fresh variable.
     */
    BasicTerm FormulaPreprocess::create_fresh_var() {
        return BasicTerm(BasicTermType::Variable, "__tmp__var_" + std::to_string(this->fresh_var_cnt++));
    }

    /**
     * @brief Replace regular sequences with a fresh variables. The regular sequence is a concatenations X1...Xk
     * such that each Xi occurrs (if it is a variable) in the
     * formula only in  X1...Xk. In other words, if we replace X1...Xk by a fresh variable V, then
     * variables from X1 ... Xk do not occurr in the formula anymore (except in V).
     *
     * @param mn Minimum number of occurrences of a regular sequence to be replaced with a fresh variable.
     */
    void FormulaPreprocess::reduce_regular_sequence(unsigned mn) {
        std::map<Concat, unsigned> regs;
        std::set<Predicate> new_eqs;
        get_regular_sublists(regs);

        for(const auto& pr : regs) {
            if(pr.second >= mn) {
                BasicTerm fresh_var = create_fresh_var();
                this->formula.replace(pr.first, Concat({fresh_var}));
                update_reg_constr(fresh_var, pr.first);
                new_eqs.insert(Predicate(PredicateType::Equation, std::vector<Concat>({Concat({fresh_var}), pr.first})));
            }
        }
        for(const Predicate& eq : new_eqs) {
            this->formula.add_predicate(eq);
            // We do not add dependency
        }
    }

    /**
     * @brief Get all epsilon terms (variables with the language containing eps only and
     * epsilon literals).
     *
     * @param res All terms with epsilon semantics.
     */
    void FormulaPreprocess::get_eps_terms(std::set<BasicTerm>& res) const {
        for(const auto& pr : get_formula().get_varmap()) {
            if(pr.first.is_variable() && is_var_eps(pr.first)) {
                res.insert(pr.first);
            }
            if(pr.first.is_literal() && pr.first.get_name() == "") {
                res.insert(pr.first);
            }

        }
    }

    /**
     * @brief Transitively ropagate epsilon variables. The epsilon variables and the epsilon
     * literal remove from the formula and set the corresponding languages appropriately.
     */
    void FormulaPreprocess::propagate_eps() {
        std::set<BasicTerm> eps_set;
        get_eps_terms(eps_set);
        std::deque<size_t> worklist;
        std::set<size_t> eps_eq_id;

        // get indices of equations containing at least one eps term
        for(const BasicTerm& t : eps_set) {
            std::set<VarNode> nds = get_formula().get_var_occurr(t);
            std::transform(nds.begin(), nds.end(), std::back_inserter(worklist),
                [](const VarNode& n){ return n.eq_index ; });
        }

        while(!worklist.empty()) {
            size_t index = worklist.front();
            worklist.pop_front();
            // eps_eq_id contains indices of equations that were reduced to eps = eps (one side is eps)
            if(eps_eq_id.find(index) != eps_eq_id.end())
                continue;

            std::set<BasicTerm> new_eps; // newly added epsilon terms
            Predicate eq = this->formula.get_predicate(index);
            if(!eq.is_equation())
                continue;

            std::set<BasicTerm> left = eq.get_left_set();
            std::set<BasicTerm> right = eq.get_right_set();
            if(is_subset(left, eps_set)) {
                new_eps = set_difference(eq.get_side_vars(Predicate::EquationSideType::Right), eps_set);
                eps_eq_id.insert(index);
            } else if(is_subset(right, eps_set)) {
                new_eps = set_difference(eq.get_side_vars(Predicate::EquationSideType::Left), eps_set);
                eps_eq_id.insert(index);
            }

            for(const BasicTerm& t : new_eps) {
                eps_set.insert(t);
                std::set<VarNode> nds = get_formula().get_var_occurr(t);
                std::transform(nds.begin(), nds.end(), std::back_inserter(worklist),
                    [](const VarNode& n){ return n.eq_index ; });
            }
        }

        for(const BasicTerm& t : eps_set) {
            if(t.is_variable()) {
                update_reg_constr(t, Concat()); // L(t) = L(t) \cap {\eps}
            }
            this->formula.replace(Concat({t}), Concat());
            // add len constraint |X| = 0
            this->len_formulae.push_back(Predicate(PredicateType::Equation, {Concat({t}), Concat()}).get_formula_eq());
            assert(t.is_variable() || t.get_name() == "");
        }
        this->formula.clean_predicates();

        // update dependencies (overapproximation). Each remaining predicate depends on all epsilon equations.
        for(const auto& pr : this->formula.get_predicates()) {
            // might result to the case {0: {0,1,...}}
            this->dependency[pr.first].insert(eps_eq_id.begin(), eps_eq_id.end());
        }


    }

    /**
     * @brief Gather information about a concatenation for equation separation.
     *
     * @param concat Concatenation
     * @param res vector where i-th position contains a pair (S,n) where S is a set of variables
     *  preceeding position i in @p concat and n is a length of all literals preceeding @p concat.
     */
    void FormulaPreprocess::get_concat_gather(const Concat& concat, SepEqsGather& res) const {
        std::pair<std::set<BasicTerm>, unsigned> prev = { std::set<BasicTerm>(), 0 };
        for(const BasicTerm& t : concat) {
            std::pair<std::set<BasicTerm>, unsigned> new_val(prev);
            if(t.is_variable()) {
                new_val.first.insert(t);
            } else if(t.is_literal()) {
                new_val.second += t.get_name().size();
            } else {
                assert(false);
            }
            res.push_back(new_val);
            prev = new_val;
        }
    }

    /**
     * @brief Separate equations into a set of new equations.
     *
     * @param eq Equation
     * @param gather_left Gathered informaiton about left side
     * @param gather_right Gathered informaiton about right side
     * @param res Set of new equations
     */
    void FormulaPreprocess::separate_eq(const Predicate& eq, const SepEqsGather& gather_left, SepEqsGather& gather_right, std::set<Predicate>& res) const {
        Concat left = eq.get_left_side();
        Concat right = eq.get_right_side();
        auto it_left = left.begin();
        auto it_right = right.begin();
        assert(eq.is_equation());

        for(size_t i = 0; i < gather_left.size(); i++) {
            for(size_t j = 0; j < gather_right.size(); j++) {
                if(gather_left[i] == gather_right[j]) {
                    res.insert(Predicate(PredicateType::Equation, std::vector<Concat>({
                        Concat(it_left, left.begin()+i+1),
                        Concat(it_right, right.begin()+j+1)
                    })));
                    it_left = left.begin()+i+1;
                    it_right = right.begin()+j+1;
                }
            }
        }
        Concat left_rest = Concat(it_left, left.end());
        Concat right_rest = Concat(it_right, right.end());
        if(left_rest.empty() && right_rest.empty()) // nothing to be added
            return;
        if(left_rest.empty())
            left_rest.push_back(BasicTerm(BasicTermType::Literal, "")); // avoid empty side by putting there epsilon
        if(right_rest.empty())
            right_rest.push_back(BasicTerm(BasicTermType::Literal, "")); // avoid empty side by putting there epsilon
        Predicate rest = Predicate(PredicateType::Equation, std::vector<Concat>({
            left_rest,
            right_rest
        }));
        res.insert(rest);
    }

    /**
     * @brief Separate equations.
     */
    void FormulaPreprocess::separate_eqs() {
        std::set<Predicate> add_eqs;
        std::set<size_t> rem_ids;
        std::map<Predicate, std::set<size_t>> deps; // local dependencies

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;
            SepEqsGather gather_left, gather_right;
            std::set<Predicate> res;
            get_concat_gather(pr.second.get_left_side(), gather_left);
            get_concat_gather(pr.second.get_right_side(), gather_right);
            separate_eq(pr.second, gather_left, gather_right, res);

            if(res.size() > 1) {
                // update dependencies of added predicates
                for(const Predicate& p : res) {
                    map_set_insert(deps, p, pr.first);
                }
                add_eqs.insert(res.begin(), res.end());
                rem_ids.insert(pr.first);
            }
        }

        for(const Predicate& p : add_eqs) {
            int index = this->formula.add_predicate(p);
            // update dependencies
            this->dependency[index] = deps[p];
        }
        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }

    }

    /**
     * @brief Gather variables allowing left/right extension. A variable X is left extensible if
     * L(X) = \Sigma^*.L(X) (right extensibility analogously). \Sigma is collected among all
     * automata in the assignment.
     *
     * @param side Left/right extension
     * @param res Extensible variables
     */
    void FormulaPreprocess::gather_extended_vars(Predicate::EquationSideType side, std::set<BasicTerm>& res) {
        Mata::Nfa::Nfa sigma_star = this->aut_ass.sigma_star_automaton();
        for(const auto& pr : this->formula.get_varmap()) {
            if(pr.second.size() > 0) {
                Mata::Nfa::Nfa concat;
                if(side == Predicate::EquationSideType::Left)
                    concat = Mata::Nfa::concatenate(sigma_star, *(this->aut_ass.at(pr.first)));
                else
                    concat = Mata::Nfa::concatenate(*(this->aut_ass.at(pr.first)), sigma_star);

                if(Mata::Nfa::are_equivalent(*(this->aut_ass.at(pr.first)), concat)) {
                    res.insert(pr.first);
                }
            }
        }
    }

    /**
     * @brief Remove extensible variables from beginning/end of an equation:
     * X = Y1 Y2 Y3 if Y1 occurrs always first (and X is the left side) and
     * Y2 is left extensible. We can remove Y1 (similarly the right extensibility and removing from
     * the end of the equation).
     */
    void FormulaPreprocess::remove_extension() {
        std::set<BasicTerm> begin_star, end_star;
        gather_extended_vars(Predicate::EquationSideType::Left, begin_star);
        gather_extended_vars(Predicate::EquationSideType::Right, end_star);

        using ExtVarMap = std::map<BasicTerm, std::vector<BasicTerm>>;
        ExtVarMap b_map, e_map;
        VarMap varmap = this->formula.get_varmap();

        auto flt = [&varmap](ExtVarMap& mp) {
            std::map<BasicTerm,BasicTerm> ret;
            for(const auto& pr : mp) {
                std::set<BasicTerm> sing(pr.second.begin(), pr.second.end());
                if(varmap[pr.first].size() == pr.second.size() && sing.size() == 1) {
                    ret.insert({pr.first, *sing.begin()});
                }
            }
            return ret;
        };

        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;
            Concat left = pr.second.get_left_side();
            Concat right = pr.second.get_right_side();
            /**
             * TODO: Extend to both sides (so far just the left side is considered)
             */
            if(left.size() == 1 && right.size() > 1) {
                if(right[0].is_variable() && left[0].is_variable()
                    && right[1].is_variable() && begin_star.find(right[1]) != begin_star.end()
                    && varmap[right[1]].size() == 1
                    && this->len_variables.find(right[0]) == this->len_variables.end()
                    && this->len_variables.find(right[1]) == this->len_variables.end() ) {
                    b_map.insert({right[0], {}});
                    b_map[right[0]].push_back(left[0]);
                }
                if(right[right.size()-1].is_variable() && left[0].is_variable()
                    && right[right.size()-2].is_variable() && end_star.find(right[right.size()-2]) != end_star.end()
                    && varmap[right[right.size()-2]].size() == 1
                    && this->len_variables.find(right[right.size()-1]) == this->len_variables.end()
                    && this->len_variables.find(right[right.size()-2]) == this->len_variables.end() ) {
                    e_map.insert({right[right.size()-1], {}});
                    e_map[right[right.size()-1]].push_back(left[0]);
                }
            }
        }

        std::map<BasicTerm,BasicTerm> b_rem = flt(b_map);
        std::map<BasicTerm,BasicTerm> e_rem = flt(e_map);
        std::map<size_t, Predicate> updates;
        for(const auto& pr : this->formula.get_predicates()) {
            Predicate pred = pr.second;
            if(!pred.is_equation()) continue;
            if(pred.get_left_side().size() > 1) continue;
            if(pred.get_right_side().size() < 2) continue;

            Concat right_side = pred.get_right_side();
            bool modif = false;
            for(const auto& beg : b_rem) {
                if(pred.get_left_side()[0] == beg.second && right_side[0] == beg.first) {
                    // X = Y1 Y2 ...
                    Concat modif_side(right_side.begin()+1, right_side.end());
                    pred = Predicate(PredicateType::Equation, std::vector<Concat>{pred.get_left_side(), modif_side} );
                    modif = true;
                    break;
                }
            }
            right_side = pred.get_right_side();
            for(const auto& end : e_rem) {
                if(pred.get_left_side()[0] == end.second && *(right_side.end()-1) == end.first) {
                    pred = Predicate(PredicateType::Equation, std::vector<Concat>{pred.get_left_side(), Concat(right_side.begin(), right_side.end()-1)} );
                    modif = true;
                    break;
                }
            }
            if(modif) updates.insert({pr.first, pred});
        }

        // We do not need to update dependencies
        for(const auto& pr : updates) {
            this->update_predicate(pr.first, pr.second);
        }
    }

    /**
     * @brief Remove trivial equations of the form X = X
     */
    void FormulaPreprocess::remove_trivial() {
        std::set<size_t> rem_ids;
        for(const auto& pr : this->formula.get_predicates()) {
            if(!pr.second.is_equation())
                continue;

            if(pr.second.get_left_side() == pr.second.get_right_side()) {
                rem_ids.insert(pr.first);
            }
        }

        for(const size_t & i : rem_ids) {
            this->formula.remove_predicate(i);
        }
    }

    /**
     * @brief Flatten dependencies. Compute transition closure of dependencies.
     *
     * @return Transitive closure of the Dependency
     */
    Dependency FormulaPreprocess::get_flat_dependency() const {
        Dependency flat = get_dependency();
        std::set<size_t> keys;
        for(const auto& pr : flat) {
            keys.insert(pr.first);
        }

        bool changed = true;
        while(changed) {
            changed = false;
            for(const size_t& k : keys) {
                auto it = flat.find(k);
                size_t sb = it->second.size();
                for(const size_t& val : flat[k]) {
                    it->second.insert(flat[val].begin(), flat[val].end());
                }
                if(sb != it->second.size()) {
                    changed = true;
                }
            }
        }

        return flat;
    }


    /**
     * @brief Return a modified formula by the preprocessing.
     *
     * @return Result of the preprocessing.
     */
    Formula FormulaPreprocess::get_modified_formula() const {
        Formula ret;
        for(const Predicate& p: this->formula.get_predicates_set()) {
            ret.add_predicate(p);
        }
        return ret;
    }



} // Namespace smt::noodler.
