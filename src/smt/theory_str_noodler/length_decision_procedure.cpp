#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa/strings.hh>

#include "util.h"
#include "aut_assignment.h"
#include "length_decision_procedure.h"

namespace smt::noodler {

    BasicTerm begin_of(zstring of, zstring from) {
        return BasicTerm(BasicTermType::Variable, "B!" + of.encode() + "_IN_" + from.encode());
    }

    bool VarConstraint::check_side(const Concat& side) {
        return side.size() == 1 && side[0].get_name() == _name;
    }

    void VarConstraint::emplace(const Concat& c, std::map<zstring, BasicTerm>& lit_conversion) {
        Concat n {};
        for (const BasicTerm& t : c) {
            if (t.is_literal()) {
                BasicTerm lit(BasicTermType::Literal, ConstraintPool::generate_lit_alias(t, lit_conversion));
                n.emplace_back(lit);
            } else {
                this->vars.insert(t);
                n.emplace_back(t);
            }
        }

        _constr_eqs.emplace_back(n);
    }

    void VarConstraint::add(const Predicate& pred, std::map<zstring, BasicTerm>& lit_conversion) {
        if (check_side(pred.get_left_side())) {
            emplace(pred.get_right_side(), lit_conversion);
            return;
        }
        if (check_side(pred.get_right_side())) {
            emplace(pred.get_left_side(), lit_conversion);
            return;
        }

        // Fresh variable 
        emplace(pred.get_right_side(), lit_conversion);
        emplace(pred.get_left_side(), lit_conversion);
    }

    const std::vector<zstring>& VarConstraint::get_lits() const {
        return _lits;
    }

    LenNode VarConstraint::generate_side_eq(const std::vector<LenNode>& side_len) const {
        LenNode left = BasicTerm(BasicTermType::Variable, this->_name);
        // if there is no variable: length is 0, for one variable the length of the right side is its length, for more the length is their sum
        LenNode right = (side_len.size() == 0) ? LenNode(0)
            : ((side_len.size() == 1) ? LenNode(side_len[0]) : LenNode(LenFormulaType::PLUS, side_len));
        return LenNode(LenFormulaType::EQ, {left, right});
    }

    /**
     * @brief Compare first n characters of l1 with last n characters of l2 (e.g. l1=banana, l2=ababa, n=2 -> [ba]nana, aba[ba] -> true)
     * 
     * @return bool match of substrings
     */
    bool VarConstraint::zstr_comp(const zstring& l1_val, const zstring& l2_val, unsigned n) {
        int s1 = 0;
        int s2 = l2_val.length() - n;

        if (s2 < 0) {
            s1 -= s2;
            n += s2;
            s2 = 0;
        }
        if (s1 + n > l1_val.length()) {
            n = l1_val.length() - s1;
        }

        for (unsigned i = 0; i < n; i++) {
            if (l1_val[s1+i] != l2_val[s2+i]) {
                return false;
            }
        }

        return true;
    }

    LenNode VarConstraint::align_literals(const zstring& l1, const zstring& l2, const std::map<zstring, BasicTerm>& conv) const {
        zstring l1_val = conv.at(l1).get_name();
        zstring l2_val = conv.at(l2).get_name();

        // both literals are just single letters
        if (l1_val.length() == 1) {
            if (l2_val.length() == 1) {
                if (l1_val[0] == l2_val[0]) {
                    return LenNode(LenFormulaType::TRUE, {});
                } else {
                    return LenNode(LenFormulaType::NOT, {LenNode(LenFormulaType::EQ, {begin_of(l1, this->_name), begin_of(l2, this->_name)})});
                }
            }
        }

        // positions (counted from l1_val) that can be overlayed with l2_val
        std::vector<unsigned> overlays{};
        for (unsigned n = 1; n <= l2_val.length() + l1_val.length() - 1; ++n) {
            if (zstr_comp(l1_val, l2_val, n)) {
                overlays.emplace_back(n);
            }
        }

        // l1 is completely before l2
        // b(l1) + |l1| <= b(l2)
        LenNode before (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(l1_val.length())}), begin_of(l2, this->_name)});
        // l2 is completely before l1
        // b(l2) + |l2| <= b(l1)
        LenNode after (LenFormulaType::LEQ, {LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())}), begin_of(l1, this->_name)});
        std::vector<LenNode> align{before, after};
        for (unsigned i : overlays) {
            // b(l1) = b(l2) + |l2| - i
            align.emplace_back(LenNode(LenFormulaType::EQ, {
                LenNode(LenFormulaType::PLUS, {begin_of(l1, this->_name), rational(i)}),
                LenNode(LenFormulaType::PLUS, {begin_of(l2, this->_name), rational(l2_val.length())})
            }));
        }

        // the literals are aligned in a way that they are completely next to each other, or they 
        // are aligned on positions given by overlays
        return LenNode(LenFormulaType::OR, align);
    }

    LenNode VarConstraint::get_lengths(const ConstraintPool& pool) const {
        std::vector<LenNode> form{};
        auto conv = pool.get_lit_conversion();

        // lits alignment
        for (const auto& a : _alignments) {
            form.emplace_back(align_literals(a.first, a.second, conv));
        }

        // kontys constraints e.g. x = uvw -> |x| = |u|+|v|+|w|
        for (const Concat& side : _constr_eqs) {
            // bool unconstrained = true;    // there are unconstrained variables
            std::vector<LenNode> side_len {};
            for (const BasicTerm& t : side) {
                if (t.is_literal()) {
                    side_len.emplace_back(conv.at(t.get_name()));
                } else {
                    side_len.emplace_back(t);
                }
            }
            form.emplace_back(generate_side_eq(side_len));
        }

        // begin constraints
        for (const Concat& side : _constr_eqs) {
            BasicTerm last (BasicTermType::Length);
            for (const BasicTerm& t : side) {
                // assume that the current left variable is y (_name). Then
                // b_y(t) = b_y(last) + |last| if last is not undef otherwise b(t) = 0
                form.emplace_back(generate_begin(t.get_name(), last, conv));
                
                // if the system is of the form y (_name) = ... x ... && x = l1 x2 l2
                // we generate b_y(l1) = b_x(l1) + b_y(x)
                if (t.is_variable() && pool.contains(t)) {
                    for (const zstring& lit : pool.at(t).get_lits()) {
                        form.emplace_back(generate_begin(lit, t.get_name()));
                    }
                }
                last = t;
            }
        }

        STRACE("str",
            tout << "Length constraints on variable " << this->_name << "\n-----\n";
            for (LenNode c : form) {
                tout << c << std::endl;
            }
            tout << "-----\n\n";
        );


        return LenNode(LenFormulaType::AND, form);
    }

    LenNode VarConstraint::get_multi_var_lia(const ConstraintPool& pool, const BasicTerm& multi_var, const BasicTerm& source_var) const {
        auto conv = pool.get_lit_conversion();
        std::vector<zstring> other_lits = this->get_lits();

        // formula saying that inside of the interval [begin, end] there is no literal in x
        auto free_formula = [&](const BasicTerm& var, const LenNode& begin, const LenNode& end) -> LenNode {
            LenNode formula(LenFormulaType::AND);
            for(const zstring& lit : other_lits) {
                LenNode or_fle(LenFormulaType::OR);
                // b_x(lit) + |lit| <= begin
                or_fle.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                    LenNode(LenFormulaType::PLUS, { begin_of(lit, this->_name), conv.at(lit) }), 
                    begin, 
                }) );
                // end <= b_x(lit)
                or_fle.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                    end,
                    begin_of(lit, this->_name), 
                }) );
                formula.succ.push_back(or_fle);
            }
            return formula;
        };

        // case when literal lit completely fits into var
        auto in_formula_case1 = [&](const BasicTerm& var, const zstring& lit) -> LenNode {
            LenNode pre1(LenFormulaType::AND);
            // b_y(var) <= b_y(lit)
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                begin_of(var.get_name(), source_var.get_name()),
                begin_of(lit, source_var.get_name()) 
            }) );
            // b_y(lit) + |lit| <= b_y(var) + |var|
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                LenNode(LenFormulaType::PLUS, { begin_of(lit, source_var.get_name()), conv.at(lit) }), 
                LenNode(LenFormulaType::PLUS, { begin_of(var.get_name(), source_var.get_name()), var }) 
            }) );

            // begin = b_x(var) + ( b_y(lit) - b_y(var) )
            LenNode begin = LenNode(LenFormulaType::PLUS, { 
                begin_of(var.get_name(), this->_name), 
                LenNode(LenFormulaType::MINUS, {
                    begin_of(lit, source_var.get_name()),
                    begin_of(var.get_name(), source_var.get_name()),
                } )
            });
            // end = begin + |lit|
            LenNode end = LenNode(LenFormulaType::PLUS, { 
                begin,
                conv.at(lit)
            });
            LenNode case1(LenFormulaType::OR, {
                LenNode(LenFormulaType::NOT, { pre1 }),
                free_formula(var, begin, end),
            });
            return case1;
        };

        // case when literal lit starts left of var and covers a part of var
        auto in_formula_case2 = [&](const BasicTerm& var, const zstring& lit) -> LenNode {
            LenNode pre1(LenFormulaType::AND);
            // b_y(lit) <= b_y(var)
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                begin_of(lit, source_var.get_name()), 
                begin_of(var.get_name(), source_var.get_name()) 
            }) );
            // b_y(var) < b_y(lit) + |lit|
            pre1.succ.push_back( LenNode(LenFormulaType::LT, { 
                begin_of(var.get_name(), source_var.get_name()),
                LenNode(LenFormulaType::PLUS, { begin_of(lit, source_var.get_name()), conv.at(lit) }), 
            }) );
            // begin = b_x(var)
            LenNode begin = begin_of(var.get_name(), this->_name);
            // end = begin + b_y(lit) + ( |lit| - b_y(var) )
            LenNode end = LenNode(LenFormulaType::PLUS, { 
                begin,
                begin_of(lit, source_var.get_name()) ,
                LenNode(LenFormulaType::MINUS, {
                    conv.at(lit),
                    begin_of(var.get_name(), source_var.get_name()),
                } )
            });
            LenNode case1(LenFormulaType::OR, {
                LenNode(LenFormulaType::NOT, { pre1 }),
                free_formula(var, begin, end),
            });
            return case1;
        };

        // case when literal lit starts inside var and exceeds the boundary of var
        auto in_formula_case3 = [&](const BasicTerm& var, const zstring& lit) -> LenNode {
            LenNode pre1(LenFormulaType::AND);
            // b_y(var) <= b_y(lit)
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                begin_of(var.get_name(), source_var.get_name()), 
                begin_of(lit, source_var.get_name()) 
            }) );
            // b_y(var) + |var| <= b_y(lit) + |lit|
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                LenNode(LenFormulaType::PLUS, { begin_of(var.get_name(), source_var.get_name()), var }),
                LenNode(LenFormulaType::PLUS, { begin_of(lit, source_var.get_name()), conv.at(lit) }), 
            }) );
            // begin = b_x(var) + ( b_y(lit) - b_y(var) )
            LenNode begin = LenNode(LenFormulaType::PLUS, { 
                begin_of(var.get_name(), this->_name), 
                LenNode(LenFormulaType::MINUS, {
                    begin_of(lit, source_var.get_name()),
                    begin_of(var.get_name(), source_var.get_name()),
                } )
            });
            // end = b_x(var) + |var|
            LenNode end = LenNode(LenFormulaType::PLUS, { 
                begin_of(var.get_name(), this->_name),
                var,
            });
            LenNode case1(LenFormulaType::OR, {
                LenNode(LenFormulaType::NOT, { pre1 }),
                free_formula(var, begin, end),
            });
            return case1;
        };

        // case when literal lit completely covers var
        auto in_formula_case4 = [&](const BasicTerm& var, const zstring& lit) -> LenNode {
            LenNode pre1(LenFormulaType::AND);
            //  b_y(lit) <= b_y(var)
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                begin_of(lit, source_var.get_name()),
                begin_of(var.get_name(), source_var.get_name()), 
            }) );
            // b_y(var) + |var| <= b_y(lit) + |lit|
            pre1.succ.push_back( LenNode(LenFormulaType::LEQ, { 
                LenNode(LenFormulaType::PLUS, { begin_of(var.get_name(), source_var.get_name()), var }),
                LenNode(LenFormulaType::PLUS, { begin_of(lit, source_var.get_name()), conv.at(lit) }), 
            }) );
            // begin = b_x(var)
            LenNode begin = begin_of(var.get_name(), this->_name);
            // end = b_x(var) + |var|
            LenNode end = LenNode(LenFormulaType::PLUS, { 
                begin_of(var.get_name(), this->_name),
                var,
            });
            LenNode case1(LenFormulaType::OR, {
                LenNode(LenFormulaType::NOT, { pre1 }),
                free_formula(var, begin, end),
            });
            return case1;
        };

        LenNode formula(LenFormulaType::AND);
        for(const zstring& lit : pool.at(source_var).get_lits()) {
            formula.succ.push_back(in_formula_case1(multi_var, lit));
            formula.succ.push_back(in_formula_case2(multi_var, lit));
            formula.succ.push_back(in_formula_case3(multi_var, lit));
            formula.succ.push_back(in_formula_case4(multi_var, lit));
        }
        return formula;
    }

    LenNode VarConstraint::generate_begin(const zstring& var_name, const BasicTerm& last, const std::map<zstring, BasicTerm>& lit_conversion) const {
        LenNode end_of_last = (last.get_type() == BasicTermType::Length)
            ? LenNode(0)
            : LenNode(LenFormulaType::PLUS, {begin_of(last.get_name(), this->_name), last.is_literal() ? lit_conversion.at(last.get_name()) : last});

        LenNode out = LenNode(LenFormulaType::EQ, {end_of_last, begin_of(var_name, this->_name)});
        return out;
    }

    LenNode VarConstraint::generate_begin(const zstring& lit, const zstring& from) const {
        // b_x(lit) = b_from(lit) + b_x(from)
        LenNode out (LenFormulaType::EQ, {begin_of(lit, this->_name), LenNode(LenFormulaType::PLUS, {begin_of(lit, from), begin_of(from, this->_name)})});
        return out;
    }

    bool VarConstraint::parse(ConstraintPool& pool) {
        if (is_parsed == l_true) {
            return true;	// Already parsed
        }
        if (is_parsed == l_undef) {
            return false;	// Cycle
        }
        is_parsed = l_undef;	// Currently in parsing

        // parse derived
        for (const Concat& side : _constr_eqs) {
            std::vector<zstring> lits_in_side {};
            for (const BasicTerm& t : side) {
                if (t.is_literal()) {
                    lits_in_side.emplace_back(t.get_name());
                } else if (t.is_variable()) {
                    // parse constrained variables
                    // the variable X occurrs on the left side of some equation
                    if (pool.count(t) > 0) {
                        if (pool[t].parse(pool) == false) {
                            return false;	// There is a cycle
                        }
                        // propagate all literals from equations corresponding to the variable X
                        for (const zstring& lit : pool[t].get_lits()) {
                            lits_in_side.emplace_back(lit);
                        }
                    }
                }
            }
            // _lits contains so-far parsed literals. 
            for (const zstring& l1 : _lits) {
                for (const zstring& l2 : lits_in_side) {
                    _alignments.emplace_back(l1, l2);
                }
            }
            for (const zstring& l : lits_in_side) {
                _lits.emplace_back(l);
            }
        }

        is_parsed = l_true;
        return true;
    }

    std::string VarConstraint::to_string() const {
        std::string ret = "#####\n# VarConstraint: " + _name.encode() + "\n###\n#";
        bool first = true;
        for (const Concat& side : _constr_eqs) {
            if (!first) {
                ret += " =";
            }
            first = false;

            for (const BasicTerm& term : side) {
                // Literals will be displayed just by their name, not by value
                ret += " " + term.to_string();
            }
        }

        ret += "\n###\n# lits:";

        for (const zstring& t :_lits) {
            // for explicit: ... lname ...
            ret += " " + t.encode();
        }

        ret += "\n#####\n";
        return ret;
    }



    static std::ostream& operator<<(std::ostream& os, const VarConstraint& vc) {
        os << vc.to_string();
        return os;
    }

    void ConstraintPool::add_to_pool(const Predicate& pred) {
        bool in_pool = false;

        for (const Concat& side : pred.get_params()) {
            if (side.size() == 1 && side[0].is_variable()) {
                BasicTerm var = side[0];
                if (this->count(var) == 0) {
                    (*this)[var] = VarConstraint(var.get_name());
                }
                (*this)[var].add(pred, this->lit_conversion);

                in_pool = true;
            }
        }

        if (!in_pool) {
            BasicTerm fresh = util::mk_noodler_var_fresh("f");
            (*this)[fresh] = VarConstraint(fresh.get_name());
            (*this)[fresh].add(pred, this->lit_conversion);
        }
    }

    ///////////////////////////////////

    lbool LengthDecisionProcedure::check_formula(std::set<BasicTerm>& multi_vars) {
        std::set<BasicTerm> concat_vars = {};	// variables that have appeared in concatenation
        
        STRACE("str", tout << " - checking suitability: "; );
        for (const Predicate& pred : this->formula.get_predicates()) {
            if (!pred.is_equation()) {
                STRACE("str", tout << "False - Inequations\n");
                return l_undef;
            }
            if (pred.mult_occurr_var_side(Predicate::EquationSideType::Left) || 
                pred.mult_occurr_var_side(Predicate::EquationSideType::Right)) {
                STRACE("str", tout << "False - multiple occurrences of a variable in single equation\n");
                return l_undef;
            }
            for (const Concat& side : pred.get_params()) {
                if (side.size() <= 1) {
                    continue;
                }

                for (const BasicTerm& t : side) {
                    if (t.is_literal()) {
                        continue;
                    }
                    if (!concat_vars.contains(t)) {
                        concat_vars.insert(t);
                    } else {
                        multi_vars.insert(t);
                        STRACE("str", tout << "multiconcat on " << t.to_string() << std::endl; );
                    }
                }
            }
        }
        return l_true;
    }

    lbool LengthDecisionProcedure::compute_next_solution() {
        STRACE("str", tout << "len: Compute next solution\n"; );

        std::set<BasicTerm> multi_vars = {};
        // Check for suitability
        if(check_formula(multi_vars) == l_undef) {
            return l_undef;
        }

        if(multi_vars.size() > 1) {
            STRACE("str", tout << "multiple vars " << std::endl; );
            return l_undef;
        }

        for (const Predicate& pred : this->formula.get_predicates()) {
            this->pool.add_to_pool(pred);
        }   

        STRACE("str",
            tout << "Conversions:\n-----\n";
            for (auto c : this->pool.get_lit_conversion()) {
                tout << c.first << " : " << c.second << std::endl;
            }
            tout << "-----\n";
        );  

        for (auto& [var, constr] : pool) {
            if (constr.parse(pool) == false) {
                // There is a cycle
                STRACE("str", tout << "len: Cyclic dependecy.\n";);
                return l_undef;	// We cannot solve this formula
            }
        }
        this->len_model = LengthProcModel(this->pool, this->subst_map, this->init_aut_ass);
        for(const BasicTerm& var : this->init_length_sensitive_vars) {
            this->len_model.add_len_var(var);
        }

        // Change if there is filler var filter
        for (const BasicTerm& v : this->formula.get_vars()) {
            // 0 <= |v|
            implicit_len_formula.emplace_back(LenNode(LenFormulaType::LEQ, {0, v}));
        }
        // generate length for each batch of equations in the pool
        for (const auto& [var, constr] : pool) {
            computed_len_formula.emplace_back(constr.get_lengths(this->pool));
        }

        // there are multiple variable occurrences --> generate LIA formula matching their values
        if(multi_vars.size() == 1) {
            // we are working with underapproximation only
            this->precision = LenNodePrecision::UNDERAPPROX;
            BasicTerm multi_var = *multi_vars.begin();
            for (const auto& [var1, constr1] : pool) {
                for (const auto& [var2, constr2] : pool) {
                    if(var1 == var2 || !constr1.get_vars().contains(multi_var) || !constr2.get_vars().contains(multi_var)) {
                        continue;
                    }
                    LenNode mult_lia = constr1.get_multi_var_lia(pool, multi_var, var2);
                    STRACE("str",
                        tout << "Multi var lia:\n-----\n";
                        tout << mult_lia << std::endl;
                        tout << "-----\n";
                    );  
                    
                    computed_len_formula.emplace_back(mult_lia);
                }
            }
        }

        STRACE("str", tout << "len: Finished computing.\n");
        return l_true;
    }

    std::pair<LenNode, LenNodePrecision> LengthDecisionProcedure::get_lengths() {
        STRACE("str", tout << "len: Get lengths\n"; );
        LenNode len_formula = LenNode(LenFormulaType::AND, {
            this->preprocessing_len_formula, 
            LenNode(LenFormulaType::AND, this->implicit_len_formula), 
            LenNode(LenFormulaType::AND, this->computed_len_formula)
        });

        for (const auto& t : init_aut_ass) {
            BasicTerm term = t.first;
            std::set<smt::noodler::BasicTerm> vars_in_eqs = this->formula.get_vars();    // Variables in all predicates

            // term does not appear in any predicate
            if (vars_in_eqs.find(term) == vars_in_eqs.end()) {
                len_formula.succ.emplace_back(this->init_aut_ass.get_lengths(term));
            }
        }

        return {len_formula, this->precision};
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {

        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params, {});

        STRACE("str", tout << "len: Preprocessing\n");

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities(); // only makes variable a literal or removes the disequation 

        AutAssignment current_ass = prep_handler.get_aut_assignment();
        mata::nfa::Nfa sigma_star = current_ass.sigma_star_automaton();
        // Underapproximate if it contains inequations
        for (const auto& [term, aut] : current_ass) {
            // we skip sigma_star automata
            if(current_ass.are_quivalent(term, sigma_star)) continue;
            if (prep_handler.get_aut_assignment().is_co_finite(term)) {
                prep_handler.underapprox_var_language(term);
                this->precision = LenNodePrecision::UNDERAPPROX;
                STRACE("str", tout << term.to_string() << " - UNDERAPPROXIMATE languages\n";);
            }
        }

        prep_handler.propagate_eps();
        prep_handler.propagate_variables(true);
        prep_handler.generate_identities();
        prep_handler.propagate_variables(true);
        prep_handler.remove_trivial();

        // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();
        this->subst_map = prep_handler.get_substitution_map();

        // propagate_eps does not mark eps variables as length variables (it is fine). If we have such variables, 
        // we need to add them to length variables explicitely (otherwise it causes probles in model generation). 
        // We also need to add remaining free variables from aut_ass in order to get their models.
        for(const auto& [term, aut] : this->init_aut_ass) {
            if(term.is_variable()) {
                this->init_length_sensitive_vars.insert(term);
            }
        }

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        if(prep_handler.contains_unsat_eqs_or_diseqs()) {
            return l_false;
        }

        if (!this->init_aut_ass.is_sat()) {
            // some automaton in the assignment is empty => we won't find solution
            return l_false;
        }

        STRACE("str",
            tout << " - formula after preprocess:\n";
            for (const Predicate& pred : this->formula.get_predicates()) {
                tout << "\t" << pred << std::endl;
            }
            tout << std::endl;
        );

        return l_undef;
    }

    bool LengthDecisionProcedure::is_suitable(const Formula &form, const AutAssignment& init_aut_ass) {
        STRACE("str", tout << "len: suitability: ";);
        for (const Predicate& pred : form.get_predicates()) {
            if(!pred.is_eq_or_ineq()) {
                STRACE("str", tout << "False - non-equation predicate\n");
                return false;
            }
        }

        // if the automata are too big --> skip the length decision procedure
        for (const auto &it : init_aut_ass) {
            if(it.second->num_of_states() > 100) {
                return false;
            }
        }

        for (const BasicTerm& t : form.get_vars()) {
            // t has language of sigma*
            if(init_aut_ass.at(t)->num_of_states() <= 1) {
                    continue;
            }

            // t is co-finite (we can underapproximate it)
            if(init_aut_ass.is_co_finite(t)) {
                continue;
            }

            // t is a literal - get shortest words
            if(init_aut_ass.is_singleton(t)) {
                continue;
            }
            STRACE("str", tout << "False - regular constraints on variable " << t << std::endl;);
            return false;
        }

        STRACE("str", tout << "True\n"; );
        return true;
    }

    zstring LengthDecisionProcedure::get_model(BasicTerm var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        if(!this->len_model.is_initialized()) {
            this->len_model.compute_model(get_arith_model_of_var);
        }
        return this->len_model.get_var_model(var);
    }

    std::vector<BasicTerm> LengthDecisionProcedure::get_len_vars_for_model(const BasicTerm& str_var) {
        return this->len_model.get_len_vars_for_model(str_var);
    }


    LengthProcModel::LengthProcModel(const ConstraintPool& block_pool, const SubstitutionMap& subst, const AutAssignment& aut_ass) : model(), subst_map(subst), aut_ass(aut_ass) {
        std::set<BasicTerm> len_vars{};
        this->lit_conversion = block_pool.get_lit_conversion();
        this->block_models = std::map<BasicTerm, BlockModel>();
        for(const auto& [block_var, var_constr] : block_pool) {
            std::set<BasicTerm> terms{};
            for (const Concat& con : var_constr.get_side_eqs()) {
                for(const BasicTerm& bt : con) {
                    terms.insert(bt);
                }
            }
            // var_constr contains also literals from children blocks (those do not occurr in the equations of the block)
            for(const zstring& lit : var_constr.get_lits()) {
                terms.insert(BasicTerm(BasicTermType::Literal, lit));
            }
            for(const BasicTerm& bt : terms) {
                if(bt.is_variable()) {
                    len_vars.insert(bt);
                }
                len_vars.insert(begin_of(bt.get_name(), block_var.get_name()));
            }
            len_vars.insert(block_var);
            this->block_models[block_var] = { "", terms };
        }
        this->length_vars = std::vector<BasicTerm>(len_vars.begin(), len_vars.end());
    }

    void LengthProcModel::generate_block_models(const BasicTerm& block_var, BlockModel& block_model, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        rational total_length = get_arith_model_of_var(block_var);
        std::vector<unsigned> solution_str(total_length.get_int32());
        for(size_t i = 0; i < total_length; i++) {
            solution_str[i] = 97; // a
        }
        for(const BasicTerm& bt : block_model.terms) {
            if(bt.is_variable()) continue;
            int lit_pos = get_arith_model_of_var(begin_of(bt.get_name(), block_var.get_name())).get_int32();
            zstring lit_val = this->lit_conversion.at(bt.get_name()).get_name();
            for(size_t i = lit_pos; i < lit_pos + lit_val.length(); i++) {
                solution_str[i] = lit_val[i - lit_pos];
            }
        }
        // convert vector of numbers to zstring
        for(size_t i = 0; i < solution_str.size(); i++) {
            block_model.solution = block_model.solution + zstring(solution_str[i]);
        }
        // so-far solution_str contains solution for x
        this->model[block_var] = block_model.solution;

        for(const BasicTerm& bt : block_model.terms) {
            if(bt.is_literal()) continue;
            int var_pos = get_arith_model_of_var(begin_of(bt.get_name(), block_var.get_name())).get_int32();
            int var_length = get_arith_model_of_var(bt).get_int32();

            zstring var_model = block_model.solution.extract(var_pos, var_length);
            this->model[bt] = var_model;
        }
    }

    void LengthProcModel::compute_model(const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        this->model.clear();
        for(auto& [block_var, block_model] : this->block_models) {
            generate_block_models(block_var, block_model, get_arith_model_of_var);
        }
        assign_subst_map_vars(get_arith_model_of_var);
        assign_free_vars(get_arith_model_of_var);
    }

    void LengthProcModel::assign_free_vars(const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        for(const BasicTerm& var : this->length_vars) {
            if(this->model.contains(var)) continue;
            if(!this->aut_ass.contains(var)) continue;
            rational total_length = get_arith_model_of_var(var);

            mata::nfa::Nfa sigma_length = this->aut_ass.sigma_automaton_of_length(total_length.get_int32());
            auto maybe_word = mata::nfa::intersection(sigma_length, *this->aut_ass.at(var)).get_word();
            if(!maybe_word.has_value()) {
                util::throw_error("empty NFA during the model generation");
            }
            mata::Word word = maybe_word.value();
            zstring res = zstring(word.size(), word.data());
            this->model[var] = res;
        }
    }

    void LengthProcModel::assign_subst_map_vars(const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        for(const auto& [term, subst] : this->subst_map) {
            if(!term.is_variable()) continue;
            this->model[term] = assign_subst_map_var(term, get_arith_model_of_var);
        }
    }

    zstring LengthProcModel::assign_aut_ass_var(const BasicTerm& var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        rational total_length = get_arith_model_of_var(var);
        mata::nfa::Nfa sigma_length = this->aut_ass.sigma_automaton_of_length(total_length.get_int32());
        auto maybe_word = mata::nfa::intersection(sigma_length, *this->aut_ass.at(var)).get_word();
        if(!maybe_word.has_value()) {
            util::throw_error("empty NFA during the model generation");
        }
        mata::Word word = maybe_word.value();
        return zstring(word.size(), word.data());
    }

    zstring LengthProcModel::assign_subst_map_var(const BasicTerm& var, const std::function<rational(BasicTerm)>& get_arith_model_of_var) {
        Concat subst = this->subst_map.at(var);
        zstring res = "";
        for(const BasicTerm& term : subst) {
            zstring val = "";
            if(term.is_literal()) {
                val = val + term.get_name();
            } else {
                // if the term is in the substitution map -> recursive call
                if(this->subst_map.contains(term)) {
                    val = assign_subst_map_var(term, get_arith_model_of_var);
                // otherwise we take the already computed model
                } else if(this->model.contains(term)) {
                    val = this->model.at(term);
                // or it is a free variable not occurring in the system solved by the length procedure
                } else {
                    val = assign_aut_ass_var(term, get_arith_model_of_var);
                }
            }
            res = res + val;
        }
        return res;
    }

}
