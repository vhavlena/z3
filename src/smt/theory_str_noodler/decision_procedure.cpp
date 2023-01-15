#include <queue>
#include <utility>
#include <mata/nfa-strings.hh>
#include "aut_assignment.h"
#include "decision_procedure.h"

namespace smt::noodler {
    DecisionProcedure::DecisionProcedure(const Formula &equalities, AutAssignment init_aut_ass, std::unordered_set<BasicTerm> init_length_sensitive_vars) {
        Mata::Nfa::Nfa aut_empty_word;
        auto state = aut_empty_word.add_state();
        aut_empty_word.make_initial(state);
        aut_empty_word.make_final(state);
        // TODO probably something with alphabet too
        automaton_with_empty_word = std::make_shared<Mata::Nfa::Nfa>(aut_empty_word);



        WorklistElement initialWlEl;
        initialWlEl.length_sensitive_vars = std::move(init_length_sensitive_vars);
        initialWlEl.aut_ass = std::move(init_aut_ass);
        // TODO the ordering of nodes_to_process right now is given by how they were added from the splitting graph, should we use something different?
        initialWlEl.inclusion_graph = std::make_shared<Graph>(Graph::create_inclusion_graph(equalities, initialWlEl.nodes_to_process)); 
        
        worklist.push_back(initialWlEl);
    }

    bool DecisionProcedure::get_another_solution() {

        while (!worklist.empty()) {
            WorklistElement element_to_process = std::move(worklist.front());
            worklist.pop_front();

            if (element_to_process.nodes_to_process.empty()) {
                // TODO do some arithmetic shit?
                return true;
            }

            std::shared_ptr<GraphNode> node_to_process = element_to_process.nodes_to_process.front();
            element_to_process.nodes_to_process.pop_front();

            bool is_node_to_process_on_cycle = element_to_process.inclusion_graph->is_on_cycle(node_to_process);

            // TODO left_side_vars can be empty, we need to do something special then
            /** process left side **/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> left_side_automata;
            const auto &left_side_vars = node_to_process->get_predicate().get_left_side();
            for (const auto &l_var : left_side_vars) {
                left_side_automata.push_back(element_to_process.aut_ass.at(l_var));
            }
            if (left_side_vars.empty()) {
                // left side is empty => left side accepts only empty word, we need to add the automaton accepting only empty word
                // it should not be problematic, there will be just one empty noodle (or none, if right side does not accept empty word)
                // so we will substitute each lenght-aware right var with empty concatenation while we process that noodle
                left_side_automata.push_back(automaton_with_empty_word);
            }
            /** end of left side processing **/


            /** Combine the right side into automata where we concatenate non-length-aware vars next to each other **/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> right_side_automata;
            const auto &right_side_vars = node_to_process->get_predicate().get_right_side();
            // each right side automaton corresponds to either concatenation of non-length-aware vars (vector of basic terms) or one lenght-aware var (vector of one basic term)
            std::vector<std::vector<BasicTerm>> right_side_division;
            bool is_there_length_on_right = false;

            if (right_side_vars.empty()) {
                // right side is empty, i.e. there is only empty word
                // because there is no length variable, it can be easily processed by FM noodlification
                // TODO do we want to do FM noodlification tho? we will end up with aut_assignment where some vars are mapped to aut accepting empty word
                right_side_automata.push_back(automaton_with_empty_word);
            } else {
                auto right_var_it = right_side_vars.begin();
                auto right_side_end = right_side_vars.end();

                std::shared_ptr<Mata::Nfa::Nfa> next_aut = std::make_shared<Mata::Nfa::Nfa>(element_to_process.aut_ass[*right_var_it]);
                std::vector<BasicTerm> next_division{ *right_var_it };
                bool last_was_length = (element_to_process.length_sensitive_vars.count(*right_var_it) > 0);
                is_there_length_on_right = last_was_length;
                ++right_var_it;

                for (; right_var_it != right_side_end; ++right_var_it) {
                    std::shared_ptr<Mata::Nfa::Nfa> right_var_aut = element_to_process.aut_ass.at(*right_var_it);
                    if (element_to_process.length_sensitive_vars.count(*right_var_it) > 0) {
                        // current right_var is length-aware
                        right_side_automata.push_back(next_aut);
                        right_side_division.push_back(next_division);
                        next_aut = right_var_aut;
                        next_division = std::vector<BasicTerm>{ *right_var_it };
                        last_was_length = true;
                        is_there_length_on_right = true;
                    } else {
                        // current right_var is not length-aware
                        if (last_was_length) {
                            right_side_automata.push_back(next_aut);
                            right_side_division.push_back(next_division);
                            next_aut = right_var_aut;
                            next_division = std::vector<BasicTerm>{ *right_var_it };
                        } else {
                            next_aut = std::make_shared<Mata::Nfa::Nfa>(Mata::Nfa::concatenate(*next_aut, *right_var_aut));
                            next_division.push_back(*right_var_it);
                            // TODO probably reduce size here
                        }
                        last_was_length = false;
                    }
                }
                right_side_automata.push_back(next_aut);
                right_side_division.push_back(next_division);
            }
            /** end of right side combining **/

            if (!is_there_length_on_right) {
                assert(right_side_automata.size() == 1);

                // we have no length-aware variables on the right hand side => we need to check if inclusion holds
                // TODO probably we should try shortest words, it might work correctly
                if (is_node_to_process_on_cycle // TODO should we not test inclusion if we have node that is not on cycle? because we will not go back to it, so it should make sense to just do noodlification
                    && Mata::Nfa::is_included(element_to_process.aut_ass.get_automaton_concat(left_side_vars), *(right_side_automata[0]))) { // there should be exactly one element in right_side_automata as we do not have length variables
                    if (element_to_process.nodes_to_process.empty()) {
                        // TODO do some other shit?
                        sat_element = std::move(element_to_process);
                        return true;
                    }
                }
            }

            // we are going to change the automata on the left side (potentially also split some on the right side, but that should not have impact)
            // so we need to add all nodes whose variable assignments are going to change on the right side (i.e. we follow inclusion graph) for processing
            for (const auto &node : element_to_process.inclusion_graph->get_edges_from(node_to_process)) {
                // we push only those nodes which are not already in nodes_to_process
                // if the node_to_process is on cycle, we need to do BFS
                // if it is not on cycle, we can do DFS
                // TODO: can we really do DFS?? 
                element_to_process.push_unique(node, is_node_to_process_on_cycle);
            }

            /* TODO check here if we have empty elements_to_process, if we do, then every noodle we get should finish and return sat
             * right now if we test sat at the beginning it should work, but it is probably better to immediatly return sat if we have
             * empty elements_to_process, however, we need to remmeber the state of the algorithm, we would need to return back to noodles
             * and process them if z3 realizes that the result is actually not sat (because of lengths)
             */
            

            if (!is_there_length_on_right) {
                // we have no length-aware variables on the right hand side
                // so we are doing only FM shit???

                assert(right_side_automata.size() == 1);

                /* TODO we call old noodlification here? we do not want unnecessary copies of inclusion graph, so this could be better, but a problem of this
                 * is that we do not process resulting empty word automata in noodles in any way, which might be a bit problematic
                 * To fix this, we could call the new noodlification and try to postpone making the copy of the inclusion graph until we actually need it
                 */
                Mata::Strings::SegNfa::NoodleSequence noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, right_side_automata[0]);
                const unsigned num_of_left_vars = left_side_vars.size();
                for (const auto &noodle : noodles) {
                    AutAssignment new_assignment;
                    for (unsigned i = 0; i < num_of_left_vars; ++i) {
                        const auto &left_var = left_side_vars[i];
                        if (new_assignment.count(left_var) == 0) {
                            new_assignment[left_var] = noodle[i];
                            // emptiness check is not needed, we only get noodles that do not have empty automata
                        } else {
                            Mata::Nfa::Nfa result = Mata::Nfa::intersection(*(new_assignment.at(left_var)), *(noodle[i]));
                            // TODO reduce_size?
                            if (Mata::Nfa::is_lang_empty(result)) {
                                // empty assignment means we end this noodle
                                continue;
                            } else {
                                new_assignment[left_var] = std::make_shared<Mata::Nfa::Nfa>(result);
                            }
                        }
                    }
                    // insert rest of vars which were not updated into new_assignment
                    new_assignment.insert(element_to_process.aut_ass.begin(), element_to_process.aut_ass.end());
                    WorklistElement new_element(std::move(new_assignment), 
                                                element_to_process.nodes_to_process,
                                                element_to_process.inclusion_graph,
                                                element_to_process.length_sensitive_vars,
                                                element_to_process.substitution_map);

                    if (new_element.nodes_to_process.empty()) {
                        // TODO do something more??
                        sat_element = std::move(new_element);
                        return true;
                    } else {
                        // TODO should we really push to front when not on cycle?
                        if (!is_node_to_process_on_cycle) {
                            worklist.push_front(new_element);
                        } else {
                            worklist.push_back(new_element);
                        }
                    }
                }
            } else {
                // we have length-aware vars on the right hand side
                // we do not test inclusion here as we need to always do splitting


                /**
                 * We get noodles where each noodle consists of automata connected with a vector of numbers
                 * So for example if we have some noodle and automaton noodle[i].first, then noodle[i].second is a vector, where first element
                 * i_l = noodle[i].second[0] tells us that automaton noodle[i].first belongs to the i_l-th left var (i.e. left_side_vars[i_l])
                 * and the second element i_r = noodle[i].second[1] tell us that it belongs to the i_r-th division of the right side (i.e. right_side_division[i_r])
                 **/
                std::vector<std::vector<std::pair<std::shared_ptr<Mata::Nfa::Nfa>, std::vector<unsigned>>>> noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, right_side_automata);

                for (const auto &noodle : noodles) {
                    WorklistElement new_element = element_to_process;
                    // we need to make a deep copy, because we will be updating this graph
                    auto new_node_to_process = new_element.make_deep_copy_of_inclusion_graph_only_nodes(node_to_process);

                    //remove processed inclusion from the inclusion graph
                    new_element.inclusion_graph->remove_node(new_node_to_process); // TODO: is this safe?

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

                    std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;

                    for (unsigned i = 0; i < right_side_division.size(); ++i) {
                        const auto &division = right_side_division[i];
                        if (division.size() == 1 && element_to_process.length_sensitive_vars.count(division[0]) != 0) {
                            // right side is length-aware variable y => we are either substituting or adding new inclusion "new_vars included in y"
                            const BasicTerm &right_var = division[0];
                            if (substitution_map.count(right_var)) {
                                // right_var is already substituted, therefore we add 'new_vars included in right_var' to the inclusion graph
                                const auto &new_inclusion = new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                                // we also add this inclusion to the worklist, as it represents unification
                                // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                                // TODO: is this correct? can we push to the front?
                                new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
                            } else {
                                // right_var is not substitued by anything yet, we will substitute it
                                substitution_map[right_var] = right_side_divisions_to_new_vars[i];
                                // as right_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                                new_element.aut_ass.erase(right_var);
                                // update the length variables
                                // TODO: is this enough to update variables only when substituting?
                                for (const BasicTerm &new_var : right_side_divisions_to_new_vars[i]) {
                                    new_element.length_sensitive_vars.insert(new_var);
                                }
                            }

                        } else {
                            // right side is non-length concatenation "y_1...y_n" => we are adding new inclusion "new_vars included in y1...y_n"
                            new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                            // we do not add the new inclusion to the worklist, because it represents the part of the inclusion that "was not split", i.e. it was processed in FM way
                        }
                    }

                    for (unsigned i = 0; i < left_side_vars.size(); ++i) {
                        const BasicTerm &left_var = left_side_vars[i];
                        if (substitution_map.count(left_var)) {
                            // left_var is already substituted, therefore we add 'left_var included in left_side_vars_to_new_vars[i]' to the inclusion graph
                            std::vector<BasicTerm> new_inclusion_left_side{ left_var };
                            const auto &new_inclusion = new_element.inclusion_graph->add_node(new_inclusion_left_side, left_side_vars_to_new_vars[i]);
                            // we also add this inclusion to the worklist, as it represents unification
                            // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                            // TODO: is this correct? can we push to the front?
                            new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
                        } else {
                            // TODO make this function or something, we do the same thing here as for the right side when substituting
                            // left_var is not substitued by anything yet, we will substitute it
                            substitution_map[left_var] = left_side_vars_to_new_vars[i];
                            // as left_var wil be substituted in the inclusion graph, we do not need to remember the automaton assignment for it
                            new_element.aut_ass.erase(left_var);
                            // update the length variables
                            // TODO: is this enough to update variables only when substituting?
                            if (new_element.length_sensitive_vars.count(left_var) > 0) { // if left_var is length-aware => substituted vars should become length-aware
                                for (const BasicTerm &new_var : left_side_vars_to_new_vars[i]) {
                                    new_element.length_sensitive_vars.insert(new_var);
                                }
                            }
                        }
                    }

                    // do substitution in the inclusion graph
                    new_element.substitute_vars(substitution_map);

                    // update inclusion graph edges
                    new_element.inclusion_graph->add_inclusion_graph_edges();

                    // update the substitution_map of new_element by the new substitutions
                    new_element.substitution_map.merge(substitution_map);

                    // TODO should we really push to front when not on cycle?
                    if (!is_node_to_process_on_cycle) {
                        worklist.push_front(new_element);
                    } else {
                        worklist.push_back(new_element);
                    }

                    // TODO: should we do something more here??

                }
                
                ++noodlification_no; // TODO: when to do this increment??
            }
        }

        return false;
    }

} // namespace smt::nodler