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
        // TODO: only generate restrictrions for length sensitive variables
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
                form.emplace_back(generate_begin(t.get_name(), last));
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

    LenNode VarConstraint::generate_begin(const zstring& var_name, const BasicTerm& last) const {
        LenNode end_of_last = (last.get_type() == BasicTermType::Length)
            ? LenNode(0)
            : LenNode(LenFormulaType::PLUS, {begin_of(last.get_name(), this->_name), last});

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

    lbool LengthDecisionProcedure::compute_next_solution() {
        STRACE("str", tout << "len: Compute next solution\n"; );

        STRACE("str",
            tout << " - formula after preprocess:\n";
            for (const Predicate& pred : this->formula.get_predicates()) {
                tout << "\t" << pred << std::endl;
            }
            tout << std::endl;
        );

        // Check for suitability
        std::vector<BasicTerm> concat_vars = {};	// variables that have appeared in concatenation
        std::set<BasicTerm> multi_vars = {};
        
        // TODO: compact to a function
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

                    // TODO: refactor
                    if (std::find(concat_vars.begin(), concat_vars.end(), t) == concat_vars.end()) {
                        concat_vars.emplace_back(t);
                        continue;
                    } else {
                        multi_vars.insert(t);
                        STRACE("str", tout << "multiconcat on " << t.to_string() << std::endl; );
                        continue;
                        // return l_undef;
                    }

                    STRACE("str", tout << "False - regular constraitns on term " << t << std::endl; );
                    return l_undef;
                }
            }
        }

        if(multi_vars.size() > 1) {
            STRACE("str", tout << "multiple vars " << std::endl; );
            return l_undef;
        }

        // End check for suitability

        STRACE("str", tout << "True\n"; );

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

        // Change if there is filler var filter
        for (const BasicTerm& v : this->formula.get_vars()) {
            // 0 <= |v|
            implicit_len_formula.emplace_back(LenNode(LenFormulaType::LEQ, {0, v}));
        }
        // generate length for each batch of equations in the pool
        for (const auto& [var, constr] : pool) {
            computed_len_formula.emplace_back(constr.get_lengths(this->pool));
        }

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

    void LengthDecisionProcedure::init_computation() {
    }

    lbool LengthDecisionProcedure::preprocess(PreprocessType opt, const BasicTermEqiv &len_eq_vars) {

        FormulaPreprocessor prep_handler(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        STRACE("str", tout << "len: Preprocessing\n");

        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities(); // only makes variable a literal or removes the disequation 

        // Underapproximate if it contains inequations
        for (const BasicTerm& t : this->formula.get_vars()) {
            if (prep_handler.get_aut_assignment().is_co_finite(t)) {
                prep_handler.underapprox_languages();
                this->precision = LenNodePrecision::UNDERAPPROX;
                STRACE("str", tout << " - UNDERAPPROXIMATE languages\n";);
                break;
            }
        }

        prep_handler.propagate_eps();
        prep_handler.propagate_variables();
        prep_handler.generate_identities();
        prep_handler.propagate_variables();
        prep_handler.remove_trivial();
        
        // Refresh the instance
        this->formula = prep_handler.get_modified_formula();
        this->init_aut_ass = prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = prep_handler.get_len_variables();
        this->preprocessing_len_formula = prep_handler.get_len_formula();

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

}