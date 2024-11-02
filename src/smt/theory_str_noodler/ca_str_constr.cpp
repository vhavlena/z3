
#include "ca_str_constr.h"
#include "formula.h"
#include "util.h"
#include <mata/nfa/delta.hh>
#include <mata/nfa/nfa.hh>
#include <mata/nfa/strings.hh>
#include <unordered_map>

namespace smt::noodler::ca {

    void DiseqAutMatrix::create_aut_matrix(const std::vector<Predicate>& disequations, const AutAssignment& aut_ass) {
        // we want to include both variables and literals
        std::set<BasicTerm> var_set;
        for (const Predicate& predicate : disequations) {
            for (const BasicTerm& var : predicate.get_vars()) {
                var_set.insert(var);
            }
        }

        // create fixed linear order of variables
        for (const BasicTerm& var : var_set) {
            this->var_order.push_back(var);
        }

        const size_t copy_cnt = 2*disequations.size() + 1;

        // set offset size
        // #Note(mhecko): What is this `+ 1` here?
        this->var_aut_init_states_in_copy.resize(copy_cnt*var_set.size() + 1);

        this->aut_matrix.resize(copy_cnt);
        for (size_t copy_idx = 0; copy_idx < copy_cnt; copy_idx++) {
            this->aut_matrix[copy_idx] = std::vector<mata::nfa::Nfa>(var_set.size());
            for (size_t var_idx = 0; var_idx < this->var_order.size(); var_idx++) {
                // @Optimize: we can avoid creating extra NFA copy here - we replace it with one symbol automaton.
                this->aut_matrix[copy_idx][var_idx] = *aut_ass.at(this->var_order[var_idx]);
            }
        }

        // Recompute the number of states that a row has
        number_of_states_in_row = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            number_of_states_in_row += this->aut_matrix[0][var_id].num_of_states();
        }

        recompute_var_aut_init_state_positions();
    }

    void DiseqAutMatrix::recompute_var_aut_init_state_positions() {
        this->var_aut_init_states_in_copy[0] = 0;

        for(size_t copy = 0; copy < this->get_copy_cnt(); copy++) {
            for(size_t var = 0; var < this->var_order.size(); var++) {
                size_t index = copy*this->var_order.size() + var;
                this->var_aut_init_states_in_copy[index + 1] = this->var_aut_init_states_in_copy[index] + this->aut_matrix[copy][var].num_of_states();
            }
        }
    }

    mata::nfa::Nfa eps_concatenate_matrix_row(const AutMatrix& matrix, size_t row_idx, std::vector<size_t>& state_var_info) {
        const std::vector<mata::nfa::Nfa>& row_elements = matrix[row_idx];
        auto elements_it = row_elements.begin();

        mata::nfa::Nfa result = *elements_it;
        elements_it++;

        for (size_t state = 0; state < result.num_of_states(); state++) {
            state_var_info[state] = 0;
        }


        size_t var_idx = 1;
        for (; elements_it != row_elements.end(); elements_it++) {
            size_t old_size = result.num_of_states();
            result = mata::nfa::concatenate(result, *elements_it, true);

            for (size_t state = old_size; state < result.num_of_states(); state++) {
                state_var_info[state] = var_idx;
            }

            var_idx += 1;
        }

        return result;
    }

    AutMatrixUnionResult DiseqAutMatrix::union_matrix() const {
        const size_t copy_count = this->get_copy_cnt();

        // #Note(mhecko): Relying on unite_nondet_with is problematic - the procedure can do all kinds of
        //                optimalizations, yet we have very clear perception of how the result should look like.
        const size_t copy_to_use_as_a_template = 0;

        size_t copy_states_cnt = 0;
        for (size_t var_id = 0; var_id < this->var_order.size(); var_id++) {
            copy_states_cnt += this->aut_matrix[copy_to_use_as_a_template][var_id].num_of_states();
        }

        std::vector<size_t> state_var_info;
        state_var_info.resize(copy_states_cnt*copy_count);

        mata::nfa::Nfa result_nfa = eps_concatenate_matrix_row(this->aut_matrix, 0, state_var_info);
        mata::nfa::Nfa latest_constructed_row_nfa;

        for (size_t copy_idx = 1; copy_idx < copy_count; copy_idx++) {
            latest_constructed_row_nfa = eps_concatenate_matrix_row(this->aut_matrix, copy_idx, state_var_info);
            result_nfa = mata::nfa::union_nondet(result_nfa, latest_constructed_row_nfa);
        }

        // State origin info for the first copy/row is ready. Propagate the origin info to the remaining copies.
        for (size_t copy_idx = 1; copy_idx < copy_count; copy_idx++) {
            for (mata::nfa::State state = 0; state < copy_states_cnt; state++) {
                state_var_info[copy_idx*copy_states_cnt + state] = state_var_info[state];
            }
        }

        result_nfa.initial = this->aut_matrix[0][0].initial;

        result_nfa.final.clear();
        size_t last_row_offset = (copy_count - 1) * copy_states_cnt;
        for (mata::nfa::State final_state : latest_constructed_row_nfa.final) {
            mata::nfa::State result_final_state = last_row_offset + final_state;
            result_nfa.final.insert(result_final_state);
        }

        // Construct info about where was a state copied from, so we can group "isomorphic" transitions later
        std::vector<size_t> where_is_state_copied_from(result_nfa.num_of_states());
        std::vector<size_t> state_levels(result_nfa.num_of_states());
        for (size_t copy_idx = 0; copy_idx < copy_count; copy_idx++) {
            const size_t template_state_cnt = latest_constructed_row_nfa.num_of_states();
            for (mata::nfa::State template_state = 0; template_state < template_state_cnt; template_state++) {
                mata::nfa::State union_state = template_state + copy_idx*template_state_cnt;
                where_is_state_copied_from[union_state] = template_state;
                state_levels[union_state] = copy_idx;
            }
        }

        TagAutStateMetadata metadata {
            .var_info = state_var_info,
            .levels   = state_levels,
            .where_is_state_copied_from = where_is_state_copied_from,
        };

        AutMatrixUnionResult result = {
            .nfa = result_nfa,
            .metadata = metadata,
        };

        return result;
    }

    //-----------------------------------------------------------------------------------------------

    void TagDiseqGen::replace_symbols(char copy_idx, size_t var) {
        BasicTerm bt = this->aut_matrix.get_var_order()[var];

        // <L,x>
        TagSet nonsampling_transition ({ ca::AtomicSymbol::create_l_symbol(bt)});
        size_t last_copy_idx = this->get_copy_cnt() - 1;
        if (copy_idx != last_copy_idx) {
            // <P,x,copy+1>
            size_t copy_idx_labeling_tag = this->get_copy_idx_labeling_transition(copy_idx, copy_idx+1);
            nonsampling_transition.insert(ca::AtomicSymbol::create_p_symbol(bt, copy_idx_labeling_tag));
        }

        mata::Symbol new_symbol = this->alph.add_symbol(nonsampling_transition);
        mata::nfa::Nfa aut = this->aut_matrix.get_aut(copy_idx, var);
        mata::nfa::Nfa res = aut.get_one_letter_aut(new_symbol);
        this->aut_matrix.set_aut(copy_idx, var, res, false);
    }

    void TagDiseqGen::add_connection_single_predicate(char copy_start, size_t var_idx, mata::nfa::Nfa& aut_union) {
        // Mapping between original symbols and new counter symbols from this->alph ensuring that the created
        // symbols are named consistently by the same mata state.
        std::map<mata::Symbol, mata::Symbol> original_to_tag_symbols;

        BasicTerm var = this->aut_matrix.get_var_order()[var_idx];

        // We use the original automaton from this->aut_ass because the actual alphabet symbols
        // might not be present in this->aut_matrix because they were replaced earlier by tags (<L, x>, etc.).
        mata::nfa::Nfa& original_automaton = *this->aut_ass.at(var);

        const size_t copy_idx_to_label_symbols_with = copy_start + 1;  // 0 is reserved for special purposes )

        for (mata::nfa::State source_state = 0; source_state < original_automaton.num_of_states(); source_state++) {
            for (const mata::nfa::SymbolPost& symbol_post : original_automaton.delta[source_state]) {
                // compute new mata symbol storing the set of AtomicSymbols
                auto original_sym_mapping_bucket = original_to_tag_symbols.find(symbol_post.symbol);

                mata::Symbol new_symbol;
                if (original_sym_mapping_bucket != original_to_tag_symbols.end()) {
                    new_symbol = original_sym_mapping_bucket->second;
                } else {
                    TagSet new_tag_set({ca::AtomicSymbol::create_l_symbol(var),
                                        ca::AtomicSymbol::create_p_symbol(var, copy_idx_to_label_symbols_with),
                                        ca::AtomicSymbol::create_r_symbol(var, copy_idx_to_label_symbols_with, symbol_post.symbol)});
                    new_symbol = this->alph.add_symbol(new_tag_set);
                    original_to_tag_symbols[symbol_post.symbol] = new_symbol;
                }

                for (const mata::nfa::State& target : symbol_post.targets) {
                    mata::nfa::State source_in_tag_aut = this->aut_matrix.get_union_state(copy_start, var_idx, source_state);
                    mata::nfa::State target_in_tag_aut = this->aut_matrix.get_union_state(copy_start+1, var_idx, target);

                    aut_union.delta.add(source_in_tag_aut, new_symbol, target_in_tag_aut);
                }
            }
        }
    }

    void TagDiseqGen::add_connection_for_multiple_predicates(char copy_start, size_t var_idx, mata::nfa::Nfa& aut_union) {
        BasicTerm var = this->aut_matrix.get_var_order()[var_idx];

        // We use the original automaton from this->aut_ass because the actual alphabet symbols
        // might not be present in this->aut_matrix because they were replaced earlier by tags (<L, x>, etc.).
        mata::nfa::Nfa& original_automaton = *this->aut_ass.at(var);

        const size_t copy_idx_to_label_symbols_with = this->get_copy_idx_labeling_transition(copy_start, copy_start+1);

        for (mata::nfa::State source_state = 0; source_state < original_automaton.num_of_states(); source_state++) {
            for (const mata::nfa::SymbolPost& symbol_post : original_automaton.delta[source_state]) {

                AtomicSymbol var_length   = AtomicSymbol::create_l_symbol(var);
                AtomicSymbol mismatch_pos = AtomicSymbol::create_p_symbol(var, copy_idx_to_label_symbols_with);

                for (size_t predicate_idx = 0; predicate_idx < this->predicates.size(); predicate_idx++) {
                    AtomicSymbol register_store_lhs = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx,
                                                                                                            AtomicSymbol::PredicateSide::LEFT,
                                                                                                            copy_idx_to_label_symbols_with,
                                                                                                            symbol_post.symbol);
                    TagSet lhs_transition_tag_set ({var_length, mismatch_pos, register_store_lhs});
                    mata::Symbol lhs_reg_store_handle = this->alph.add_symbol(lhs_transition_tag_set);

                    AtomicSymbol register_store_rhs = ca::AtomicSymbol::create_r_symbol_with_predicate_info(predicate_idx,
                                                                                                            AtomicSymbol::PredicateSide::RIGHT,
                                                                                                            copy_idx_to_label_symbols_with,
                                                                                                            symbol_post.symbol);
                    TagSet rhs_transition_tag_set ({var_length, mismatch_pos, register_store_rhs});
                    mata::Symbol rhs_reg_store_handle = this->alph.add_symbol(rhs_transition_tag_set);

                    for (const mata::nfa::State& target : symbol_post.targets) {
                        mata::nfa::State source_in_tag_aut = this->aut_matrix.get_union_state(copy_start, var_idx, source_state);
                        mata::nfa::State target_in_tag_aut = this->aut_matrix.get_union_state(copy_start+1, var_idx, target);

                        aut_union.delta.add(source_in_tag_aut, rhs_reg_store_handle, target_in_tag_aut);
                        aut_union.delta.add(source_in_tag_aut, lhs_reg_store_handle, target_in_tag_aut);
                    }
                }
            }
        }

        if (this->predicates.size() == 1) return;  // We don't add copy transitions when we are dealing with a single predicate
        if (copy_start == 0) return;

        for (size_t predicate_idx = 0; predicate_idx < this->predicates.size(); predicate_idx++) {
            ca::AtomicSymbol copy_for_lhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, ca::AtomicSymbol::PredicateSide::LEFT,  copy_idx_to_label_symbols_with);
            ca::AtomicSymbol copy_for_rhs = ca::AtomicSymbol::create_c_symbol(var, predicate_idx, ca::AtomicSymbol::PredicateSide::RIGHT, copy_idx_to_label_symbols_with);

            // There is no need to cache the symbols - we know that every (var, copy_idx) will have a single unique Copy symbol
            mata::Symbol sym_handle_for_lhs = this->alph.add_symbol({copy_for_lhs});
            mata::Symbol sym_handle_for_rhs = this->alph.add_symbol({copy_for_rhs});

            for (mata::nfa::State source_state_rel = 0; source_state_rel < original_automaton.num_of_states(); source_state_rel++) {
                mata::nfa::State source_state_abs = this->aut_matrix.get_union_state(copy_start,   var_idx, source_state_rel);
                mata::nfa::State dest_state_abs   = this->aut_matrix.get_union_state(copy_start+1, var_idx, source_state_rel);

                aut_union.delta.add(source_state_abs, sym_handle_for_lhs, dest_state_abs);
                aut_union.delta.add(source_state_abs, sym_handle_for_rhs, dest_state_abs);
            }
        }
    }

    ca::TagAut TagDiseqGen::construct_tag_aut() {
        const std::vector<BasicTerm>& var_order = this->aut_matrix.get_var_order();
        const size_t copy_cnt = this->get_copy_cnt();

        // update symbols for each inner automaton
        for (char copy = 0; copy < copy_cnt; copy++) {
            for (size_t var = 0; var < var_order.size(); var++) {
                // replace each automaton in the matrix with the specific AtomicSymbol
                replace_symbols(copy, var);
            }
        }

        // union all automata in the matrix
        AutMatrixUnionResult nfa_with_metadata = this->aut_matrix.union_matrix();

        // add mata epsilon symbol to alphabet. Used for DOT export.
        this->alph.insert(mata::nfa::EPSILON, {});

        // generate connecting transitions
        if (this->predicates.size() == 1) {
            for (char copy_idx = 0; copy_idx < copy_cnt - 1; copy_idx++) {
                for (size_t var_idx = 0; var_idx < var_order.size(); var_idx++) {
                    this->add_connection_single_predicate(copy_idx, var_idx, nfa_with_metadata.nfa);
                }
            }
        } else {
            for (char copy_idx = 0; copy_idx < copy_cnt - 1; copy_idx++) {
                for (size_t var_idx = 0; var_idx < var_order.size(); var_idx++) {
                    this->add_connection_for_multiple_predicates(copy_idx, var_idx, nfa_with_metadata.nfa);
                }
            }
        }

        // Trim the automaton
        if (this->predicates.size() == 1) {
            size_t original_nfa_size = nfa_with_metadata.nfa.num_of_states();

            std::unordered_map<mata::nfa::State, mata::nfa::State> state_renaming; // Original state -> New state

            nfa_with_metadata.nfa.trim(&state_renaming);  // Automaton is modified in-place

            size_t new_nfa_size = nfa_with_metadata.nfa.num_of_states();

            TagAutStateMetadata new_metadata;
            new_metadata.levels.resize(new_nfa_size);
            new_metadata.var_info.resize(new_nfa_size);
            new_metadata.where_is_state_copied_from.resize(new_nfa_size);

            for (mata::nfa::State original_state = 0; original_state < original_nfa_size; original_state++) {
                auto rename_entry_it = state_renaming.find(original_state);
                if (rename_entry_it == state_renaming.end()) {
                    continue; // State has been removed
                }

                mata::nfa::State new_state = rename_entry_it->second;

                new_metadata.levels[new_state]   = nfa_with_metadata.metadata.levels[original_state];
                new_metadata.var_info[new_state] = nfa_with_metadata.metadata.var_info[original_state];
                new_metadata.where_is_state_copied_from[new_state] = nfa_with_metadata.metadata.where_is_state_copied_from[original_state];
            }

            nfa_with_metadata.metadata = std::move(new_metadata);
        }

        TagAut result = {
            nfa_with_metadata.nfa,
            this->alph,
            var_order,
            nfa_with_metadata.metadata
        };

        return result;
    }

    //-----------------------------------------------------------------------------------------------


    //-----------------------------------------------------------------------------------------------

    LenNode get_lia_for_disequations(const Formula& diseqs, const AutAssignment& autass) {
        if(diseqs.get_predicates().size() == 0) {
            return LenNode(LenFormulaType::TRUE);
        }

        FormulaPreprocessor prep_handler{diseqs, autass, {}, {}, {}};
        prep_handler.propagate_eps();
        prep_handler.remove_trivial();
        prep_handler.reduce_diseqalities();

        if(prep_handler.get_modified_formula().get_predicates().size() == 0) {
            if(prep_handler.get_aut_assignment().is_sat()) {
                return LenNode(LenFormulaType::TRUE);
            }
            return LenNode(LenFormulaType::FALSE);
        }

        if (autass.empty()) {
            STRACE("str-diseq", tout << "Aut assignment is empty, cannot build formula.\n");
            assert(!autass.empty());
        }

        Predicate diseq = prep_handler.get_modified_formula().get_predicates()[0];
        TagDiseqGen gen(diseq, prep_handler.get_aut_assignment());
        ca::TagAut tag_aut = gen.construct_tag_aut();
        tag_aut.nfa.trim();
        STRACE("str-diseq",
            tout << "* Disequation: " << diseq << std::endl;
        );

        STRACE("str-diseq",
            tout << "* Variable ordering: " << std::endl;
            tout << concat_to_string(gen.get_aut_matrix().get_var_order()) << std::endl << std::endl;
        );

        STRACE("str-diseq",
            tout << "* NFAs for variables: " << std::endl;
            for(const BasicTerm& bt : diseq.get_set()) {
                tout << bt.to_string() << ":" << std::endl;
                autass.at(bt)->print_to_dot(tout);
            }
            tout << std::endl;
        );
        STRACE("str-diseq",
            tout << "* Tag Automaton for diseq: " << diseqs.to_string() << std::endl;
            tag_aut.print_to_dot(tout);
            tout << std::endl;
        );
        STRACE("str", tout << "TagAut LIA: finished" << std::endl; );

        // we include only those symbols occurring in the reduced tag automaton
        std::set<AtomicSymbol> ats;
        for (const auto& trans : tag_aut.nfa.delta.transitions()) {
            std::set<AtomicSymbol> sms = tag_aut.alph.get_symbol(trans.symbol);
            ats.insert(sms.begin(), sms.end());
        }

        parikh::ParikhImageDiseqTag pi(tag_aut, ats, 0);
        LenNode pi_formula = pi.get_diseq_formula(diseq);

        STRACE("str-diseq", tout << "* Resulting formula: " << std::endl << pi_formula << std::endl << std::endl; );

        return pi_formula;
    }

    std::pair<LenNode, LenNodePrecision> get_lia_for_not_contains(const Formula& formula, const AutAssignment& var_assignment) {

        if (formula.get_predicates().empty()) {
            return { LenNode(LenFormulaType::TRUE), LenNodePrecision::PRECISE };
        }

        FormulaPreprocessor prep_handler{formula, var_assignment, {}, {}, {}};
        prep_handler.propagate_eps();

        bool is_not_contains_obviously_false = !prep_handler.replace_not_contains();
        bool is_not_contains_syntactically_false = prep_handler.can_unify_not_contains();

        if (is_not_contains_obviously_false || is_not_contains_syntactically_false) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::PRECISE };
        }

        if (formula.get_predicates().size() > 1) {
            // We have more than 1 notContains, for now we pretent we don't know what to do with it
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        const Predicate& not_contains = formula.get_predicates().at(0);

        // #Optimize(mhecko): Add a Iterator<const BasicTerm> to Predicate - it is pointless to create a set
        std::set<BasicTerm> vars = not_contains.get_set();

        bool can_construct_lia = true;
        for (const BasicTerm& var : vars) {
            if (var.get_type() == BasicTermType::Literal) {
                // var is a literal - right now we do not support that.
                STRACE("str-not-contains", tout << "* not-contains has a literal - we do not support literals yet\n"; );
                can_construct_lia = false;
                break;
            }

            if (!var_assignment.is_flat(var)) {
                STRACE("str-not-contains", tout << "* cannot reduce to LIA - one of the input vars does not have a flat langauge\n"; );
                can_construct_lia = false;
                break;

            };
        }

        if (!can_construct_lia) {
            return { LenNode(LenFormulaType::FALSE), LenNodePrecision::UNDERAPPROX };
        }

        AutAssignment actual_var_assignment = prep_handler.get_aut_assignment();

        // Preprocess the assignment: reduce the automata and make them deterministic
        for (auto it = actual_var_assignment.begin(); it != actual_var_assignment.end(); it++) {
            mata::nfa::Nfa reduced_nfa = mata::nfa::reduce(*it->second);
            mata::nfa::Nfa reduced_dfa = mata::nfa::determinize(reduced_nfa);
            it->second = std::make_shared<mata::nfa::Nfa>(reduced_dfa);
            STRACE("str-not-contains", {
                tout << "* (var assignment) NFA assigned to " << it->first << ":\n";
                it->second->print_to_dot(tout);
            });
        }

        ca::TagDiseqGen tag_automaton_generator(not_contains, actual_var_assignment);

        ca::TagAut tag_automaton = tag_automaton_generator.construct_tag_aut();
        std::set<AtomicSymbol> atomic_symbols = tag_automaton.gather_used_symbols();

        STRACE("str-not-contains",
            tout << "* tag automaton: \n";
            tag_automaton.print_to_dot(tout);
            tout << std::endl;
        );

        size_t num_of_states_in_row = tag_automaton_generator.get_aut_matrix().get_number_of_states_in_row();
        parikh::ParikhImageNotContTag not_contains_generator(tag_automaton,
                                                             atomic_symbols,
                                                             num_of_states_in_row);

        LenNode not_contains_formula = not_contains_generator.get_not_cont_formula(not_contains);

        STRACE("str-not-contains",
            tout << "* generated formula: \n";
            tout << not_contains_formula << std::endl;
        );

        return { not_contains_formula, LenNodePrecision::PRECISE };
    }

}

// Questions for noodler devs:
// - how to introduce a new variable (so that the var handle will not be conflicting with any other variables)
