#include <queue>
#include <utility>
#include <mata/nfa-strings.hh>
#include "aut_assignment.h"
#include "decision_procedure.h"

namespace smt::noodler {
    void DecisionProcedure::initialize(const Instance& inst) {
        WorklistElement initialWlEl;
        initialWlEl.length_sensitive_vars = get_length_sensitive_vars(inst); // TODO how????
        initialWlEl.aut_ass = get_init_aut_ass(inst); // TODO how????
        Formula equalities = get_equalities(inst); // TODO how????
        initialWlEl.inclusion_graph = std::make_shared<Graph>(Graph::create_inclusion_graph(equalities, initialWlEl.nodes_to_process)); 
        // TODO: should we add initial nodes to the nodes we want to process (the order of processing might be a bit weird then), or should we add all nodes here and get the order based on the creation of inclusion graph
        // initialWlEl.nodes_to_process.insert(initialWlEl.nodes_to_process.end(), initialWlEl.inclusion_graph->initial_nodes.begin(), initialWlEl.inclusion_graph->initial_nodes.end());
        // some mapping of variables to vector of variables (representing substituting after splitting)???? => this might work only for chain-free

        worklist.push(initialWlEl);
    }

    bool DecisionProcedure::get_another_solution(const Instance& inst, LengthConstr& out) {

        while (!worklist.empty()) {
            WorklistElement element_to_process = std::move(worklist.front());
            worklist.pop_front();

            if (element_to_process.nodes_to_process.empty()) {
                // TODO do some arithmetic shit
                return true;
            }

            std::shared_ptr<GraphNode> node_to_process = element_to_process.nodes_to_process.front();
            element_to_process.nodes_to_process.pop_front();

            // TODO add check if both sides are same; if they are, just remove
            
            /** Combine the right side into automata where we concatenate non-length-aware vars next to each other **/
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> right_side_automata;
            // each right side automaton corresponds to either concatenation of non-length-aware vars (vector of basic terms) or one lenght-aware var (vector of one basic term)
            std::vector<std::vector<BasicTerm>> right_side_division;

            assert(!node_to_process->get_predicate().get_right_side().empty()); // TODO: we should be able to process even situation where right/left side is empty (i.e. representing empty word)
            auto right_var_it = node_to_process->get_predicate().get_right_side().begin();
            auto right_side_end = node_to_process->get_predicate().get_right_side().end();

            std::shared_ptr<Mata::Nfa::Nfa> next_aut = std::make_shared<Mata::Nfa::Nfa>(element_to_process.aut_ass[*right_var_it]);
            std::vector<BasicTerm> next_division{ *right_var_it };
            bool last_was_length = (element_to_process.length_sensitive_vars.count(*right_var_it) > 0);
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
            /** end of right side combining **/
            
            std::vector<std::shared_ptr<Mata::Nfa::Nfa>> left_side_automata;
            const auto &left_side_vars = node_to_process->get_predicate().get_left_side();
            for (const auto &l_var : left_side_vars) {
                left_side_automata.push_back(element_to_process.aut_ass.at(l_var));
            }

            bool is_node_to_process_on_cycle = element_to_process.inclusion_graph->is_on_cycle(node_to_process);

            for (const auto &node : element_to_process.inclusion_graph->edges.at(node_to_process)) {
                if (is_node_to_process_on_cycle) {
                    // if the node_to_process is on cycle, we need to do BFS
                    element_to_process.push_back_unique(node);
                } else {
                    // if it is not on cycle, we can do DFS
                    // TODO: can we really do DFS?? 
                    element_to_process.push_front_unique(node);
                }
            }
            

            if (right_side_automata.size() == 1) {
                // we have no length-aware variables on the right hand side
                // so we are doing only FM shit???
                
                // TODO test inclusion (should we do it if we have node that is not on cycle? and what about shortest words, now we probably have to do the prorper inclusion?)
                // after succesful test we should probably check if element_to_process.nodes_to_process contained only node_to_process, if yes => sat


                Mata::Strings::SegNfa::NoodleSequence noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, right_side_automata); // we call old noodlification here? or should we somehow process if we get automata accepting empty words
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
                    new_assignment.add_to_assignment(element_to_process.aut_ass);
                    WorklistElement new_element(std::move(new_assignment), 
                                                element_to_process.nodes_to_process,
                                                element_to_process.inclusion_graph,
                                                element_to_process.length_sensitive_vars);
                    worklist.push(new_element);
                }
            } else {
                // we have length-aware vars on the right hand side
                // we do not test inclusion here as we need to always do splitting


                /**
                 * TODO: I do not know how noodlification works yet, I assume I will get noodles where each noodle is connected with some pairs of numbers
                 * So for example if we have some noodle and automaton noodle[i].first, then noodle[i].second is a pair, where first element
                 * i_l = noodle[i].second.first tells us that automaton noodle[i].first belongs to the i_l-th left var (i.e. left_side_vars[i_l])
                 * and the second element i_r = noodle[i].second.second tell us that it belongs to the i_r-th division of the right side (i.e. right_side_division[i_r])
                 **/
                std::vector<std::vector<std::pair<std::shared_ptr<Mata::Nfa::Nfa>, std::pair<unsigned,unsigned>>>> noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side_automata, right_side_automata);

                for (const auto &noodle : noodles) {
                    WorklistElement new_element = element_to_process;
                    // we need to make a deep copy, because we will be updating this graph
                    new_element.make_deep_copy_of_inclusion_graph_only_nodes();

                    std::vector<std::vector<BasicTerm>> left_side_vars_to_new_vars(left_side_vars.size());
                    std::vector<std::vector<BasicTerm>> right_side_divisions_to_new_vars(right_side_division.size());
                    for (unsigned i = 0; i < noodle.size(); ++i) {
                        // TODO do not make a new_var if we can replace it with left or right var (i.e. new_var is exactly left or right var)
                        BasicTerm new_var(BasicTermType::Variable, VAR_PREFIX + std::string("_") + std::to_string(noodlification_no) + std::string("_") + std::to_string(i));
                        left_side_vars_to_new_vars[noodle[i].second.first].push_back(new_var);
                        right_side_divisions_to_new_vars[noodle[i].second.second].push_back(new_var);
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
                            for (const BasicTerm &new_var : left_side_vars_to_new_vars[i]) {
                                new_element.length_sensitive_vars.insert(new_var);
                            }
                        }
                    }

                    //remove processed inclusion from the inclusion graph
                    new_element.inclusion_graph->remove_node(node_to_process); // TODO: is this safe?

                    // do substitution in the inclusion graph
                    new_element.substitute_vars(substitution_map);

                    // update inclusion graph edges
                    new_element.inclusion_graph->add_inclusion_graph_edges();

                    // update the substitution_map of new_element by the new substitutions
                    new_element.substitution_map.merge(substitution_map);

                    // TODO should we push to front when not on cycle?
                    if (!is_node_to_process_on_cycle) {
                        worklist.push_front(new_element);
                    } else {
                        worklist.push_back(new_element);
                    }

                    // TODO: should we do something more here??

                    ++noodlification_no; // TODO: when to do this increment??

                }
            }
        }

        return false;
    }



    bool is_sat_FM(const Graph &inclusion_graph, const AutAssignment &initial_assignments) {
        std::queue<std::pair<AutAssignment, std::queue<const GraphNode*>>> branches;

        std::queue<const GraphNode*> initial_nodes;
        for (const auto &node : inclusion_graph.nodes) {
            // which nodes to push???
            initial_nodes.push(&node);
        }
        branches.push(std::make_pair(initial_assignments, std::move(initial_nodes)));

        while (branches.size() != 0) {
            std::pair<AutAssignment, std::queue<const GraphNode*>> branch = std::move(branches.front());
            branches.pop();

            if (branch.second.empty()) {
                //probably save the state of solving here??
                return true;
            }

            const GraphNode *inclusion_to_check = branch.second.front();
            branch.second.pop();

            Mata::Nfa::Nfa right_side = branch.first.get_automaton_concat(inclusion_to_check->get_predicate().get_right_side());
            
            //Mata::Nfa::Nfa left_side = branch.first.get_automaton_concat(inclusion_to_check.get_predicate().get_left_side());
            // TODO!!!!! TEST shortest_words_of_left_side is subset of right_side



            Mata::Nfa::AutPtrSequence left_side;
            for (const auto &l_var : inclusion_to_check->get_predicate().get_left_side()) {
                left_side.push_back(branch.first.at(l_var).get());
            }
            

            // auto it = inclusion_to_check.get_predicate().get_left_side().begin();
            // auto end = inclusion_to_check.get_predicate().get_left_side().end();
            // Mata::Nfa::Nfa left_side = *it;
            // ++it;
            // for (; it != end; ++it) {
            //     left_side = Mata::Nfa::concatenate(left_side, branch.first.at(*it), true);
            // }

            std::queue vertices_to_check = branch.second;
            for (const auto &vertex : inclusion_graph.edges.at(const_cast<GraphNode*>(inclusion_to_check))) {
                vertices_to_check.push(vertex);
            }

            auto noodles = Mata::Strings::SegNfa::noodlify_for_equation(left_side, right_side);//, false, Mata::Nfa::StringMap{{"reduce", "forward"}})
            for (const auto &noodle : noodles) {
                const auto &left_side_vars = inclusion_to_check->get_predicate().get_left_side();
                const unsigned num_of_left_vars = left_side_vars.size();
                AutAssignment newAssignment;
                for (unsigned i = 0; i < num_of_left_vars; ++i) {
                    const auto &left_var = left_side_vars[i];
                    if (newAssignment.count(left_var) == 0) {
                        newAssignment[left_var] = noodle[i];
                        // emptiness check is not needed, we only get noodles that do not have empty automata
                    } else {
                        Mata::Nfa::Nfa result = Mata::Nfa::intersection(*(newAssignment.at(left_var)), *(noodle[i]));
                        // TODO simulation?
                        if (Mata::Nfa::is_lang_empty(result)) {
                            // ??? empty assignment means we end this noodle?
                            continue;
                        } else {
                            newAssignment[left_var] = std::make_shared<Mata::Nfa::Nfa>(result);
                        }
                    }
                }
                newAssignment.add_to_assignment(branch.first);
                branches.push(std::make_pair(newAssignment, vertices_to_check));
            }
        }
    }
}