#include <queue>
#include <utility>
#include <algorithm>
#include <functional>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "decision_procedure.h"

namespace smt::noodler {

    void SolvingState::substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map) {
        // substitutes variables in a vector using substitution_map
        auto substitute_vector = [&substitution_map](const std::vector<BasicTerm> &vector) {
            std::vector<BasicTerm> result;
            for (const BasicTerm &var : vector) {
                if (substitution_map.count(var) == 0) {
                    result.push_back(var);
                } else {
                    const auto &to_this = substitution_map.at(var);
                    result.insert(result.end(), to_this.begin(), to_this.end());
                }
            }
            return result;
        };

        // substitutes variables in both sides of inclusion using substitution_map
        auto substitute_inclusion = [&substitute_vector](const Predicate &inclusion) {
            std::vector<BasicTerm> new_left_side = substitute_vector(inclusion.get_left_side());
            std::vector<BasicTerm> new_right_side = substitute_vector(inclusion.get_right_side());
            return Predicate{inclusion.get_type(), { new_left_side, new_right_side }};
        };

        // returns true if the inclusion has the same thing on both sides
        auto inclusion_has_same_sides = [](const Predicate &inclusion) { return inclusion.get_left_side() == inclusion.get_right_side(); };

        // substitutes variables of inclusions in a vector using substitute_map, but does not keep the ones that have the same sides after substitution
        auto substitute_set = [&substitute_inclusion, &inclusion_has_same_sides](const std::set<Predicate> inclusions) {
            std::set<Predicate> new_inclusions;
            for (const auto &old_inclusion : inclusions) {
                auto new_inclusion = substitute_inclusion(old_inclusion);
                if (!inclusion_has_same_sides(new_inclusion)) {
                    new_inclusions.insert(new_inclusion);
                }
            }
            return new_inclusions;
        };

        inclusions = substitute_set(inclusions);
        inclusions_not_on_cycle = substitute_set(inclusions_not_on_cycle);

        // substituting inclusions to process is bit harder, it is possible that two inclusions that were supposed to
        // be processed become same after substituting, so we do not want to keep both in inclusions to process
        std::set<Predicate> substituted_inclusions_to_process;
        std::deque<Predicate> new_inclusions_to_process;
        while (!inclusions_to_process.empty()) {
            Predicate substituted_inclusion = substitute_inclusion(inclusions_to_process.front());
            inclusions_to_process.pop_front();
            
            if (!inclusion_has_same_sides(substituted_inclusion) // we do not want to add inclusion that is already in inclusions_to_process
                && substituted_inclusions_to_process.count(substituted_inclusion) == 0) {
                new_inclusions_to_process.push_back(substituted_inclusion);
            }
        }
        inclusions_to_process = new_inclusions_to_process;
    }

    AutAssignment SolvingState::flatten_substition_map() {
        AutAssignment result = aut_ass;
        std::function<std::shared_ptr<Mata::Nfa::Nfa>(const BasicTerm&)> flatten_var;

        flatten_var = [&result, &flatten_var, this](const BasicTerm &var) -> std::shared_ptr<Mata::Nfa::Nfa> {
            if (result.count(var) == 0) {
                std::shared_ptr<Mata::Nfa::Nfa> var_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::create_empty_string_nfa());
                for (const auto &subst_var : this->substitution_map.at(var)) {
                    var_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*var_aut, *flatten_var(subst_var)));
                }
                result[var] = var_aut;
                return var_aut;
            } else {
                return result[var];
            }
        };
        for (const auto &subst_map_pair : substitution_map) {
            flatten_var(subst_map_pair.first);
        }
        STRACE("str-nfa",
            tout << "Flattened substitution map:" << std::endl;
            for (const auto &var_aut : result) {
                tout << "Var " << var_aut.first.get_name() << std::endl;
                var_aut.second->print_to_DOT(tout);
            });
        return result;
    }

    DecisionProcedure::DecisionProcedure(ast_manager& m, seq_util& m_util_s, arith_util& m_util_a, const theory_str_noodler_params& par) 
        : prep_handler(Formula(), AutAssignment(), {}, par), m{ m }, m_util_s{ m_util_s },
        m_util_a{ m_util_a },
        init_length_sensitive_vars{ },
        formula { },
        m_params(par),
        init_aut_ass{ } {
    }

    bool DecisionProcedure::compute_next_solution() {
        // iteratively select next state of solving that can lead to solution and
        // process one of the unprocessed nodes (or possibly find solution)
        STRACE("str", tout << "------------------------"
                           << "Getting another solution"
                           << "------------------------" << std::endl;);

        while (!worklist.empty()) {
            SolvingState element_to_process = std::move(worklist.front());
            worklist.pop_front();

            if (element_to_process.inclusions_to_process.empty()) {
                // we found another solution, element_to_process contain the automata
                // assignment and variable substition that satisfy the original
                // inclusion graph
                solution = std::move(element_to_process);
                return true;
            }

            // we will now process one inclusion from the inclusion graph which is at front
            // i.e. we will update automata assignments and substitutions so that this inclusion is fulfilled
            Predicate inclusion_to_process = element_to_process.inclusions_to_process.front();
            element_to_process.inclusions_to_process.pop_front();

            // this will decide whether we will continue in our search by DFS or by BFS
            bool is_inclusion_to_process_on_cycle = element_to_process.is_inclusion_on_cycle(inclusion_to_process);

            STRACE("str", tout << "Processing node with inclusion " << inclusion_to_process << " which is" << (is_inclusion_to_process_on_cycle ? " " : " not ") << "on the cycle" << std::endl;);
            STRACE("str",
                tout << "Length variables are:";
                for(auto const &var : inclusion_to_process.get_vars()) {
                    if (element_to_process.length_sensitive_vars.count(var)) {
                        tout << " " << var.to_string();
                    }
                }
                tout << std::endl;
            );

            const auto &left_side_vars = inclusion_to_process.get_left_side();
            const auto &right_side_vars = inclusion_to_process.get_right_side();

            /********************************************************************************************************/
            /****************************************** One side is empty *******************************************/
            /********************************************************************************************************/
            // As kinda optimization step, we do "noodlification" for empty sides separately (i.e. sides that
            // represent empty string). This is because it is simpler, we would get only one noodle so we just need to
            // check that the non-empty side actually contains empty string and replace the vars on that side by epsilon.
            if (right_side_vars.empty() || left_side_vars.empty()) {
                std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;
                auto const non_empty_side_vars = right_side_vars.empty() ? 
                                                        inclusion_to_process.get_left_set()
                                                      : inclusion_to_process.get_right_set();
                bool non_empty_side_contains_empty_word = true;
                for (const auto &var : non_empty_side_vars) {
                    if (Mata::Nfa::is_in_lang(*element_to_process.aut_ass.at(var), {{}, {}})) {
                        // var contains empty word, we substitute it with only empty word, but only if...
                        if (right_side_vars.empty() // ...non-empty side is the left side (var is from left) or...
                               || element_to_process.length_sensitive_vars.count(var) > 0 // ...var is length-aware
                         ) {
                            assert(substitution_map.count(var) == 0 && element_to_process.aut_ass.count(var) > 0);
                            // we prepare substitution for all vars on the left or only the length vars on the right
                            // (as non-length vars are probably not needed? TODO: would it make sense to update non-length vars too?)
                            substitution_map[var] = {};
                            element_to_process.aut_ass.erase(var);
                        }
                    } else {
                        // var does not contain empty word => whole non-empty side cannot contain empty word
                        non_empty_side_contains_empty_word = false;
                        break;
                    }
                }
                if (!non_empty_side_contains_empty_word) {
                    // in the case that the non_empty side does not contain empty word
                    // the inclusion cannot hold (noodlification would not create anything)
                    continue;
                }

                // TODO: all this following shit is done also during normal noodlification, I need to split it to some better defined functions

                element_to_process.remove_inclusion(inclusion_to_process);

                // We might be updating left side, in that case we need to process all nodes that contain the variables from the left,
                // i.e. those nodes to which inclusion_to_process goes to. In the case we are updating right side, there will be no edges
                // coming from inclusion_to_process, so this for loop will do nothing.
                for (const auto &dependent_inclusion : element_to_process.get_dependent_inclusions(inclusion_to_process)) {
                    // we push only those nodes which are not already in inclusions_to_process
                    // if the inclusion_to_process is on cycle, we need to do BFS
                    // if it is not on cycle, we can do DFS
                    // TODO: can we really do DFS??
                    element_to_process.push_unique(dependent_inclusion, is_inclusion_to_process_on_cycle);
                }

                // do substitution in the inclusion graph
                element_to_process.substitute_vars(substitution_map);
                // update the substitution_map of new_element by the new substitutions
                element_to_process.substitution_map.merge(substitution_map);

                // TODO: should we really push to front when not on cycle?
                // TODO: maybe for this case of one side being empty, we should just push to front?
                if (!is_inclusion_to_process_on_cycle) {
                    worklist.push_front(element_to_process);
                } else {
                    worklist.push_back(element_to_process);
                }
                continue;
            }
            /********************************************************************************************************/
            /*************************************** End of one side is empty ***************************************/
            /********************************************************************************************************/



            /********************************************************************************************************/
            /****************************************** Process left side *******************************************/
            /********************************************************************************************************/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> left_side_automata;
            STRACE("str-nfa", tout << "Left automata:" << std::endl);
            for (const auto &l_var : left_side_vars) {
                left_side_automata.push_back(element_to_process.aut_ass.at(l_var));
                STRACE("str-nfa",
                    tout << "Automaton for left var " << l_var.get_name() << ":" << std::endl;
                    left_side_automata.back()->print_to_DOT(tout);
                );
            }
            /********************************************************************************************************/
            /************************************** End of left side processing *************************************/
            /********************************************************************************************************/




            /********************************************************************************************************/
            /***************************************** Process right side *******************************************/
            /********************************************************************************************************/
            // We combine the right side into automata where we concatenate non-length-aware vars next to each other.
            // Each right side automaton corresponds to either concatenation of non-length-aware vars (vector of
            // basic terms) or one lenght-aware var (vector of one basic term). Division then contains for each right
            // side automaton the variables whose concatenation it represents.
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> right_side_automata;
            std::vector<std::vector<BasicTerm>> right_side_division;

            assert(!right_side_vars.empty()); // empty case was processed at the beginning
            auto right_var_it = right_side_vars.begin();
            auto right_side_end = right_side_vars.end();

            std::shared_ptr<Mata::Nfa::Nfa> next_aut = element_to_process.aut_ass[*right_var_it];
            std::vector<BasicTerm> next_division{ *right_var_it };
            bool last_was_length = (element_to_process.length_sensitive_vars.count(*right_var_it) > 0);
            bool is_there_length_on_right = last_was_length;
            ++right_var_it;

            STRACE("str-nfa", tout << "Right automata:" << std::endl);
            for (; right_var_it != right_side_end; ++right_var_it) {
                std::shared_ptr<Mata::Nfa::Nfa> right_var_aut = element_to_process.aut_ass.at(*right_var_it);
                if (element_to_process.length_sensitive_vars.count(*right_var_it) > 0) {
                    // current right_var is length-aware
                    right_side_automata.push_back(next_aut);
                    right_side_division.push_back(next_division);
                    STRACE("str-nfa",
                        tout << "Automaton for right var(s)";
                        for (const auto &r_var : next_division) {
                            tout << " " << r_var.get_name();
                        }
                        tout << ":" << std::endl;
                        next_aut->print_to_DOT(tout);
                    );
                    next_aut = right_var_aut;
                    next_division = std::vector<BasicTerm>{ *right_var_it };
                    last_was_length = true;
                    is_there_length_on_right = true;
                } else {
                    // current right_var is not length-aware
                    if (last_was_length) {
                        // if last var was length-aware, we need to add automaton for it into right_side_automata
                        right_side_automata.push_back(next_aut);
                        right_side_division.push_back(next_division);
                        STRACE("str-nfa",
                            tout << "Automaton for right var(s)";
                            for (const auto &r_var : next_division) {
                                tout << " " << r_var.get_name();
                            }
                            tout << ":" << std::endl;
                            next_aut->print_to_DOT(tout);
                        );
                        next_aut = right_var_aut;
                        next_division = std::vector<BasicTerm>{ *right_var_it };
                    } else {
                        // if last var was not length-aware, we combine it (and possibly the non-length-aware vars before)
                        // with the current one
                        next_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*next_aut, *right_var_aut));
                        next_division.push_back(*right_var_it);
                        // TODO should we reduce size here?
                    }
                    last_was_length = false;
                }
            }
            right_side_automata.push_back(next_aut);
            right_side_division.push_back(next_division);
            STRACE("str-nfa",
                tout << "Automaton for right var(s)";
                for (const auto &r_var : next_division) {
                    tout << " " << r_var.get_name();
                }
                tout << ":" << std::endl;
                next_aut->print_to_DOT(tout);
            );
            /********************************************************************************************************/
            /************************************* End of right side processing *************************************/
            /********************************************************************************************************/


            /********************************************************************************************************/
            /****************************************** Inclusion test **********************************************/
            /********************************************************************************************************/
            if (!is_there_length_on_right) {
                // we have no length-aware variables on the right hand side => we need to check if inclusion holds
                assert(right_side_automata.size() == 1); // there should be exactly one element in right_side_automata as we do not have length variables
                // TODO probably we should try shortest words, it might work correctly
                if (is_inclusion_to_process_on_cycle // we do not test inclusion if we have node that is not on cycle, because we will not go back to it (TODO: should we really not test it?)
                    && Mata::Nfa::is_included(element_to_process.aut_ass.get_automaton_concat(left_side_vars), *right_side_automata[0])) {
                    // TODO can I push to front? I think I can, and I probably want to, so I can immediately test if it is not sat (if element_to_process.inclusions_to_process is empty), or just to get to sat faster
                    worklist.push_front(element_to_process);
                    // we continue as there is no need for noodlification, inclusion already holds
                    continue;
                }
            }
            /********************************************************************************************************/
            /*************************************** End of inclusion test ******************************************/
            /********************************************************************************************************/

            element_to_process.remove_inclusion(inclusion_to_process);

            // We are going to change the automata on the left side (potentially also split some on the right side, but that should not have impact)
            // so we need to add all nodes whose variable assignments are going to change on the right side (i.e. we follow inclusion graph) for processing.
            // Warning: Self-loops are not in inclusion graph, but we might still want to add this node again to inclusions_to_process, however, this node will be
            // split during noodlification, so we will only add parts whose right sides actually change (see below in noodlification)
            for (const auto &node : element_to_process.get_dependent_inclusions(inclusion_to_process)) {
                // we push only those nodes which are not already in inclusions_to_process
                // if the inclusion_to_process is on cycle, we need to do BFS
                // if it is not on cycle, we can do DFS
                // TODO: can we really do DFS??
                element_to_process.push_unique(node, is_inclusion_to_process_on_cycle);
            }
            // We will need the set of left vars, so we can sort the 'non-existing self-loop' in noodlification (see previous warning)
            const auto left_vars_set = inclusion_to_process.get_left_set();


            /* TODO check here if we have empty elements_to_process, if we do, then every noodle we get should finish and return sat
             * right now if we test sat at the beginning it should work, but it is probably better to immediatly return sat if we have
             * empty elements_to_process, however, we need to remmeber the state of the algorithm, we would need to return back to noodles
             * and process them if z3 realizes that the result is actually not sat (because of lengths)
             */

            

            /********************************************************************************************************/
            /******************************************* Noodlification *********************************************/
            /********************************************************************************************************/
            /**
             * We get noodles where each noodle consists of automata connected with a vector of numbers.
             * So for example if we have some noodle and automaton noodle[i].first, then noodle[i].second is a vector,
             * where first element i_l = noodle[i].second[0] tells us that automaton noodle[i].first belongs to the
             * i_l-th left var (i.e. left_side_vars[i_l]) and the second element i_r = noodle[i].second[1] tell us that
             * it belongs to the i_r-th division of the right side (i.e. right_side_division[i_r])
             **/
            auto noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, 
                                                                        right_side_automata,
                                                                        false, 
                                                                        {{"reduce", "true"}});

            for (const auto &noodle : noodles) {
                STRACE("str", tout << "Processing noodle" << std::endl; );
                SolvingState new_element = element_to_process;

                /* Explanation of the next code on an example:
                 * Left side has variables x_1, x_2, x_3, x_2 while the right side has variables x_4, x_1, x_5, x_6, where x_1
                 * and x_4 are length-aware (i.e. there is one automaton for concatenation of x_5 and x_6 on the right side).
                 * Assume that noodle represents the case where it was split like this:
                 *              | x_1 |    x_2    | x_3 |       x_2       |
                 *              | t_1 | t_2 | t_3 | t_4 | t_5 |    t_6    |
                 *              |    x_4    |       x_1       | x_5 | x_6 |
                 * In the following for loop, we create the vars t1, t2, ..., t6 and prepare two vectors left_side_vars_to_new_vars
                 * and right_side_divisions_to_new_vars which map left vars and right divisions into the concatenation of the new
                 * vars. So for example left_side_vars_to_new_vars[1] = t_2 t_3, because second left var is x_2 and we map it to t_2 t_3,
                 * while right_side_divisions_to_new_vars[2] = t_6, because the third division on the right represents the automaton for
                 * concatenation of x_5 and x_6 and we map it to t_6.
                 */
                std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars(left_side_vars.size());
                std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars(right_side_division.size());
                for (unsigned i = 0; i < noodle.size(); ++i) {
                    // TODO do not make a new_var if we can replace it with one left or right var (i.e. new_var is exactly left or right var)
                    // TODO also if we can substitute with epsilon, we should do that first? or generally process epsilon substitutions better, in some sort of 'preprocessing'
                    BasicTerm new_var(BasicTermType::Variable, VAR_PREFIX + std::string("_") + std::to_string(noodlification_no) + std::string("_") + std::to_string(i));
                    left_side_vars_to_new_vars[noodle[i].second[0]].push_back(new_var);
                    right_side_divisions_to_new_vars[noodle[i].second[1]].push_back(new_var);
                    new_element.aut_ass[new_var] = noodle[i].first; // we assign the automaton to new_var
                }

                // Each variable that occurs in the left side or is length-aware needs to be substituted, we use this map for that 
                std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

                /* Following the example from before, the following loop will create these inclusions from the right side divisions:
                 *         t_1 t_2 ⊆ x_4
                 *     t_3 t_4 t_5 ⊆ x_1
                 *             t_6 ⊆ x_5 x_6
                 * However, we do not add the first two inclusions into the inclusion graph but use them for substitution, i.e.
                 *        substitution_map[x_4] = t_1 t_2
                 *        substitution_map[x_1] = t_3 t_4 t_5
                 * because they are length-aware vars.
                 */
                for (unsigned i = 0; i < right_side_division.size(); ++i) {
                    const auto &division = right_side_division[i];
                    if (division.size() == 1 && element_to_process.length_sensitive_vars.count(division[0]) != 0) {
                        // right side is length-aware variable y => we are either substituting or adding new inclusion "new_vars ⊆ y"
                        const BasicTerm &right_var = division[0];
                        if (substitution_map.count(right_var)) {
                            // right_var is already substituted, therefore we add 'new_vars ⊆ right_var' to the inclusion graph
                            // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                            const auto &new_inclusion = new_element.add_inclusion(right_side_divisions_to_new_vars[i], division, is_inclusion_to_process_on_cycle);
                            // we also add this inclusion to the worklist, as it represents unification
                            // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                            // TODO: is this correct? can we push to the front?
                            // TODO: can't we push to front even if it is on cycle??
                            new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                            STRACE("str", tout << "added new inclusion from the right side because it could not be substituted: " << new_inclusion << std::endl; );
                        } else {
                            // right_var is not substitued by anything yet, we will substitute it
                            substitution_map[right_var] = right_side_divisions_to_new_vars[i];
                            STRACE("str", tout << "right side var " << right_var.get_name() << " replaced with:"; for (auto const &var : right_side_divisions_to_new_vars[i]) { tout << " " << var.get_name(); } tout << std::endl; );
                            // as right_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                            new_element.aut_ass.erase(right_var);
                            // update the length variables
                            for (const BasicTerm &new_var : right_side_divisions_to_new_vars[i]) {
                                new_element.length_sensitive_vars.insert(new_var);
                            }
                        }

                    } else {
                        // right side is non-length concatenation "y_1...y_n" => we are adding new inclusion "new_vars ⊆ y1...y_n"
                        // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                        // TODO: do we need to add inclusion if previous node was not on cycle? because I think it is not possible to get to this new node anyway
                        const auto &new_inclusion = new_element.add_inclusion(right_side_divisions_to_new_vars[i], division, is_inclusion_to_process_on_cycle);
                        // we add this inclusion to the worklist only if the right side contains something that was on the left (i.e. it was possibly changed)
                        if (SolvingState::is_dependent(left_vars_set, new_inclusion.get_right_set())) {
                            // TODO: again, push to front? back? where the fuck to push??
                            new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                        }
                        STRACE("str", tout << "added new inclusion from the right side (non-length): " << new_inclusion << std::endl; );
                    }
                }

                /* Following the example from before, the following loop will create these inclusions from the left side:
                 *           x_1 ⊆ t_1
                 *           x_2 ⊆ t_2 t_3
                 *           x_3 ⊆ t_4
                 *           x_2 ⊆ t_5 t_6
                 * Again, we want to use the inclusions for substitutions, but we replace only those variables which were
                 * not substituted yet, so the first inclusion stays (x_1 was substituted from the right side) and the
                 * fourth inclusion stays (as we substitute x_2 using the second inclusion). So from the second and third
                 * inclusion we get:
                 *        substitution_map[x_2] = t_2 t_3
                 *        substitution_map[x_3] = t_4
                 */
                for (unsigned i = 0; i < left_side_vars.size(); ++i) {
                    // TODO maybe if !is_there_length_on_right, we should just do intersection and not create new inclusions
                    const BasicTerm &left_var = left_side_vars[i];
                    if (left_var.is_literal()) {
                        // we skip literals, we do not want to substitute them
                        continue;
                    }
                    if (substitution_map.count(left_var)) {
                        // left_var is already substituted, therefore we add 'left_var ⊆ left_side_vars_to_new_vars[i]' to the inclusion graph
                        std::vector<BasicTerm> new_inclusion_left_side{ left_var };
                        // TODO: how to decide if sometihng is on cycle? by previous node being on cycle, or when we recompute inclusion graph edges?
                        const auto &new_inclusion = new_element.add_inclusion(new_inclusion_left_side, left_side_vars_to_new_vars[i], is_inclusion_to_process_on_cycle);
                        // we also add this inclusion to the worklist, as it represents unification
                        // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                        // TODO: is this correct? can we push to the front?
                        // TODO: can't we push to front even if it is on cycle??
                        new_element.push_unique(new_inclusion, is_inclusion_to_process_on_cycle);
                        STRACE("str", tout << "added new inclusion from the left side because it could not be substituted: " << new_inclusion << std::endl; );
                    } else {
                        // TODO make this function or something, we do the same thing here as for the right side when substituting
                        // left_var is not substitued by anything yet, we will substitute it
                        substitution_map[left_var] = left_side_vars_to_new_vars[i];
                        STRACE("str", tout << "left side var " << left_var.get_name() << " replaced with:"; for (auto const &var : left_side_vars_to_new_vars[i]) { tout << " " << var.get_name(); } tout << std::endl; );
                        // as left_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                        new_element.aut_ass.erase(left_var);
                        // update the length variables
                        if (new_element.length_sensitive_vars.count(left_var) > 0) { // if left_var is length-aware => substituted vars should become length-aware
                            for (const BasicTerm &new_var : left_side_vars_to_new_vars[i]) {
                                new_element.length_sensitive_vars.insert(new_var);
                            }
                        }
                    }
                }

                // do substitution in the inclusion graph
                new_element.substitute_vars(substitution_map);

                // update the substitution_map of new_element by the new substitutions
                new_element.substitution_map.merge(substitution_map);

                // TODO should we really push to front when not on cycle?
                if (!is_inclusion_to_process_on_cycle) {
                    worklist.push_front(new_element);
                } else {
                    worklist.push_back(new_element);
                }

            }

            ++noodlification_no; // TODO: when to do this increment?? maybe noodlification_no should be part of SolvingState?
            /********************************************************************************************************/
            /*************************************** End of noodlification ******************************************/
            /********************************************************************************************************/

        }

        // there are no solving states left, which means nothing led to solution -> it must be unsatisfiable
        return false;
    }

    expr_ref DecisionProcedure::get_length_from_solving_state(const std::map<BasicTerm, expr_ref>& variable_map, const SolvingState &state, const std::unordered_set<smt::noodler::BasicTerm> &vars) {
        expr_ref lengths(m.mk_true(), m);
        
        for(const BasicTerm& var : vars) {
            
            // get the z3 variable from var
            expr_ref z3_var(this->m);
            auto it = variable_map.find(var);
            if(it != variable_map.end()) {
                // take the existing variable from the map
                z3_var = m_util_s.str.mk_length(it->second);
            } else {
                // if the variable is not found, it was introduced during preprocessing or decision procedure
                // we therefore create a z3 variable using the name of var
                z3_var = util::mk_int_var(var.get_name().encode(), this->m, this->m_util_s, this->m_util_a);
            }

            // add |z3_var| >= 0, important probably only for the case that var was introduced during preprocessing
            // or decision procedure, existing z3 vars should have this already in the LIA solver
            lengths = m.mk_and(lengths, m_util_a.mk_ge(z3_var, m_util_a.mk_int(0)));

            if (state.aut_ass.count(var) > 0) {
                // if var is not substituted, get length constraint from its automaton
                std::set<std::pair<int, int>> aut_constr = Mata::Strings::get_word_lengths(*state.aut_ass.at(var));
                lengths = this->m.mk_and(lengths, mk_len_aut(z3_var, aut_constr));
            } else if (state.substitution_map.count(var) > 0) {
                // if var is substituted, then we have to create length equation
                // i.e. if state.substitution_map[var] = x_1 x_2 ... x_n, then we create |var| = |x_1| + |x_2| + ... + |x_n|

                // translate each x_i to z3 var and create the sum |x_1| + |x_2| + ... + |x_n|
                expr_ref sum(m_util_a.mk_int(0), m);
                for(const BasicTerm&x_i : state.substitution_map.at(var)) {
                    expr_ref z3_x_i(this->m);
                    auto varit = variable_map.find(x_i);
                    if(varit != variable_map.end()) {
                        // take the existing variable from the map
                        z3_x_i = m_util_s.str.mk_length(varit->second);
                    } else {
                        // if the variable is not found, it was introduced during preprocessing or decision procedure
                        // we therefore create a z3 variable using the name of x_i
                        z3_x_i = util::mk_int_var(x_i.get_name().encode(), this->m, this->m_util_s, this->m_util_a);
                    }

                    sum = m_util_a.mk_add(sum, z3_x_i);
                }
                lengths = m.mk_and(lengths, m.mk_eq(z3_var, sum));

            } else {
                util::throw_error("Variable was neither in automata assignment nor was substituted");
            }
        }

        return lengths;
    }

    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions
     */
    expr_ref DecisionProcedure::get_lengths(const std::map<BasicTerm, expr_ref>& variable_map) {
        expr_ref lengths(m.mk_true(), m);

        // collect lengths introduced by the preprocessing
        expr_ref prep_formula = util::len_to_expr(
                this->prep_handler.get_len_formula(),
                variable_map,
                this->m, this->m_util_s, this->m_util_a );
        lengths = this->m.mk_and(lengths, prep_formula);

        if(this->solution.aut_ass.size() == 0) {
            // if the decision procedure was not run yet, we return lengths of the initial assignment TODO rewrite
            lengths = this->m.mk_and(lengths, get_length_from_solving_state(variable_map, worklist.front(), worklist.front().aut_ass.get_keys()));
        } else {
            // TODO explain

            lengths = this->m.mk_and(lengths, get_length_from_solving_state(variable_map, solution, solution.length_sensitive_vars));

            // check whether disequalities are satisfiable
            // adds length constraint (|L| != |R| or (|x_1| == |x_2| and check_diseq(a_1,a_2)))
            // where L = x_1 a_1 y_1 and R = x_2 a_2 y_2 were created during FormulaPreprocess::replace_disequalities()
            lengths = this->m.mk_and(lengths, len_diseqs(ass, variable_map));
            
        }

        return lengths;
    }

    bool DecisionProcedure::check_diseq(const AutAssignment& ass, const std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map, const std::pair<BasicTerm, BasicTerm>& pr) {
        std::function<std::vector<BasicTerm>(const smt::noodler::BasicTerm&)> get_substituted_var;
        get_substituted_var = [](const smt::noodler::BasicTerm &var) {
            if (substitution_map)
            return var;
        }

        auto get_symbol_word = [](const Nfa &nfa) {
            // get all one-symbol words accepted by nfa assuming
            // that nfa accepts words of size 0 and 1
            nfa.trim();
            std::set<Mata::Symbol> symbols;
            for (const auto &tran : nfa.delta) {
                symbols.insert(tran.symb);
            }
            return symbols;
        };

        auto s1 = get_symbol_word(*ass.at(pr.first));
        auto s2 = get_symbol_word(*ass.at(pr.second));
        STRACE("str", tout << "diseq check s1:"; for (const auto s1el : s1) {tout << " " << s1el;} tout << std::endl << "diseq check s2:"; for (const auto s2el : s2) {tout << " " << s2el;} tout << std::endl;);
        if((s1.size() == 0 || s2.size() == 0) || // if one of the variables was only epsilon, the original sides of disequation have to have different lengths, so here we return false
            (s1.size() == 1 && s2.size() == 1 && s1 == s2) // if we can only assign the same symbol to the variables, it is unsat
          ) {
            return false;
        }
        return true;
    }

    expr_ref DecisionProcedure::len_diseqs(const AutAssignment& ass, const std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map, const std::map<BasicTerm, expr_ref>& variable_map) {
        expr_ref ret(this->m.mk_true(), this->m);
        for(const auto& pr: this->prep_handler.get_diseq_len()) {
            expr_ref f1 = util::len_to_expr(
                pr.second.first,
                variable_map,
                this->m, this->m_util_s, this->m_util_a );
            expr_ref f2 = util::len_to_expr(
                pr.second.second,
                variable_map,
                this->m, this->m_util_s, this->m_util_a );
            expr_ref dis_check(this->m.mk_true(), this->m);
            if(!check_diseq(ass, substitution_map, pr.first)) {
                dis_check = this->m.mk_false();
            }
            ret = this->m.mk_and(ret, this->m.mk_or(f2, this->m.mk_and(f1, dis_check)));
        }
        return ret;
    }

    /**
     * @brief Creates initial inclusion graph according to the preprocessed instance.
     */
    void DecisionProcedure::init_computation() {
        SolvingState initialWlEl;
        initialWlEl.length_sensitive_vars = this->init_length_sensitive_vars;
        initialWlEl.aut_ass = std::move(this->init_aut_ass);

        if(!initialWlEl.aut_ass.is_sat()) { // TODO: return unsat core
            return;
        }

        if (!this->formula.get_predicates().empty()) {
            // TODO we probably want to completely get rid of inclusion graphs
            std::deque<std::shared_ptr<GraphNode>> tmp;
            Graph incl_graph = Graph::create_inclusion_graph(this->formula, tmp);
            for (auto const &node : incl_graph.get_nodes()) {
                initialWlEl.inclusions.insert(node->get_predicate());
                if (!incl_graph.is_on_cycle(node)) {
                    initialWlEl.inclusions_not_on_cycle.insert(node->get_predicate());
                }
            }
            // TODO the ordering of inclusions_to_process right now is given by how they were added from the splitting graph, should we use something different? also it is not deterministic now, depends on hashes
            while (!tmp.empty()) {
                initialWlEl.inclusions_to_process.push_back(tmp.front()->get_predicate());
                tmp.pop_front();
            }
        }

        worklist.push_back(initialWlEl);
    }

    /**
     * @brief Preprocessing.
     */
    void DecisionProcedure::preprocess(PreprocessType opt) {
        // As a first preprocessing operation, convert string literals to fresh variables with automata assignment
        //  representing their string literal.
        conv_str_lits_to_fresh_lits();
        this->prep_handler = FormulaPreprocess(this->formula, this->init_aut_ass, this->init_length_sensitive_vars, m_params);

        // So-far just lightweight preprocessing
        this->prep_handler.propagate_variables();
        this->prep_handler.propagate_eps();
        this->prep_handler.remove_regular();
        this->prep_handler.skip_len_sat();
        this->prep_handler.generate_identities();
        this->prep_handler.propagate_variables();
        this->prep_handler.refine_languages();
        this->prep_handler.reduce_diseqalities();
        this->prep_handler.remove_trivial();
        this->prep_handler.reduce_regular_sequence(3);
        this->prep_handler.remove_regular();
        // underapproximation
        if(opt == PreprocessType::UNDERAPPROX) {
            this->prep_handler.underapprox_languages();
            this->prep_handler.skip_len_sat();
            this->prep_handler.reduce_regular_sequence(3);
            this->prep_handler.remove_regular();
            this->prep_handler.skip_len_sat();
        }
        // replace disequalities
        this->prep_handler.replace_disequalities();

        // Refresh the instance
        this->init_aut_ass = this->prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = this->prep_handler.get_len_variables();
        this->formula = this->prep_handler.get_modified_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        STRACE("str", tout << "preprocess-output:" << std::endl << this->formula.to_string() << std::endl; );
    }

    /**
     * @brief Make a length constraint for a single NFA loop, handle
     *
     * @param var variable
     * @param v1 handle
     * @param v2 loop
     * @return expr_ref Length formula
     */
    expr_ref DecisionProcedure::mk_len_aut_constr(const expr_ref& var, int v1, int v2) {
        expr_ref len_x(var, this->m);
        expr_ref k = util::mk_int_var_fresh("k", this->m, this->m_util_s, this->m_util_a);
        expr_ref c1(this->m_util_a.mk_int(v1), this->m);
        expr_ref c2(this->m_util_a.mk_int(v2), this->m);

        if(v2 != 0) {
            expr_ref right(this->m_util_a.mk_add(c1, this->m_util_a.mk_mul(k, c2)), this->m);
            return expr_ref(this->m.mk_and(this->m.mk_eq(len_x, right), this->m_util_a.mk_ge(k, this->m_util_a.mk_int(0))), this->m);
        }
        return expr_ref(this->m.mk_eq(len_x, c1), this->m);
    }

    /**
     * @brief Make a length formula corresponding to a set of pairs <loop, handle>
     *
     * @param var Variable
     * @param aut_constr Set of pairs <loop, handle>
     * @return expr_ref Length constaint of the automaton
     */
    expr_ref DecisionProcedure::mk_len_aut(const expr_ref& var, std::set<std::pair<int, int>>& aut_constr) {
        expr_ref res(this->m.mk_false(), this->m);
        for(const auto& cns : aut_constr) {
            res = this->m.mk_or(res, mk_len_aut_constr(var, cns.first, cns.second));
        }
        res = expr_ref(this->m.mk_and(res, this->m_util_a.mk_ge(var, this->m_util_a.mk_int(0))), this->m);
        return res;
    }

    /**
     * @brief Set new instance for the decision procedure.
     * 
     * @param equalities Equalities
     * @param init_aut_ass Initial automata assignment
     * @param init_length_sensitive_vars Length sensitive vars
     */
    void DecisionProcedure::set_instance(const Formula &equalities, AutAssignment &init_aut_ass, const std::unordered_set<BasicTerm>& init_length_sensitive_vars) {
        this->init_length_sensitive_vars = init_length_sensitive_vars;
        this->formula = equalities;
        this->init_aut_ass = init_aut_ass;
        this->prep_handler = FormulaPreprocess(equalities, init_aut_ass, init_length_sensitive_vars, m_params);
    }

    void DecisionProcedure::conv_str_lits_to_fresh_lits() {
        size_t counter{ 0 };
        std::map<zstring, zstring> str_literals{};
        for (auto& predicate : formula.get_predicates()) {
            if (predicate.is_eq_or_ineq()) {
                conv_str_lits_to_fresh_lits_for_side(predicate.get_left_side(), counter, str_literals);
                conv_str_lits_to_fresh_lits_for_side(predicate.get_right_side(), counter, str_literals);
            }
        }
    }

    void DecisionProcedure::conv_str_lits_to_fresh_lits_for_side(
        std::vector<BasicTerm>& side, size_t& fresh_lits_counter, std::map<zstring, zstring>& converted_str_literals) {
        constexpr char name_prefix[]{ "fresh_str_lit_" };
        for (auto& term : side) {
            if (term.is_literal()) { // Handle string literal.
                BasicTerm fresh_literal{ BasicTermType::Literal };
                auto fresh_literal_iter{ converted_str_literals.find(term.get_name()) };
                if (fresh_literal_iter != converted_str_literals.end()) {
                    fresh_literal.set_name(fresh_literal_iter->second);
                } else {
                    std::string fresh_name{ name_prefix + std::to_string(fresh_lits_counter) };
                    fresh_literal.set_name(fresh_name);
                    ++fresh_lits_counter;
                    Nfa nfa{ util::create_word_nfa(term.get_name()) };
                    init_aut_ass.emplace(fresh_literal, std::make_shared<Nfa>(std::move(nfa)));
                    converted_str_literals.emplace(term.get_name(), fresh_name);
                }

                term = fresh_literal;
            }
        }
    }

    DecisionProcedure::DecisionProcedure(
             const Formula &equalities, AutAssignment init_aut_ass,
             const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
             ast_manager& m, seq_util& m_util_s, arith_util& m_util_a,
             const theory_str_noodler_params& par
     ) : prep_handler(equalities, init_aut_ass, init_length_sensitive_vars, par), m{ m }, m_util_s{ m_util_s },
     m_util_a{ m_util_a },
     init_length_sensitive_vars{ init_length_sensitive_vars },
         formula { equalities },
         init_aut_ass{ init_aut_ass },
         m_params(par) {
         }

} // Namespace smt::noodler.
