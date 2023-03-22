#include <queue>
#include <utility>
#include <algorithm>

#include <mata/nfa-strings.hh>
#include "util.h"
#include "aut_assignment.h"
#include "decision_procedure.h"

namespace smt::noodler {
    std::shared_ptr<GraphNode> SolvingState::make_deep_copy_of_inclusion_graph_only_nodes(std::shared_ptr<GraphNode> processed_node) {
        assert(inclusion_graph->get_nodes().count(processed_node) > 0);
        Graph graph_to_copy = *inclusion_graph;
        graph_to_copy.remove_all_edges();
        assert(graph_to_copy.get_nodes().count(processed_node) > 0);
        std::unordered_map<std::shared_ptr<GraphNode>, std::shared_ptr<GraphNode>> node_mapping;
        inclusion_graph = std::make_shared<Graph>(graph_to_copy.deep_copy(node_mapping));
        std::deque<std::shared_ptr<GraphNode>> new_nodes_to_process;
        while (!nodes_to_process.empty()) {
            new_nodes_to_process.push_back(node_mapping.at(nodes_to_process.front()));
            nodes_to_process.pop_front();
        }
        nodes_to_process = new_nodes_to_process;
        return node_mapping.at(processed_node);
    }

    void SolvingState::substitute_vars(std::unordered_map<BasicTerm, std::vector<BasicTerm>> &substitution_map) {
        std::unordered_set<std::shared_ptr<GraphNode>> deleted_nodes;
        inclusion_graph->substitute_vars(substitution_map, deleted_nodes);

        // remove all deleted_nodes from the nodes_to_process (using remove/erase)
        // TODO: is this correct?? I assume that if we delete copy of a merged node from nodes_to_process, it either does not need to be processed or the merged node will be in nodes_to_process
        auto is_deleted = [&deleted_nodes](std::shared_ptr<GraphNode> node) { return (deleted_nodes.count(node) > 0) ; };
        nodes_to_process.erase(std::remove_if(nodes_to_process.begin(), nodes_to_process.end(), is_deleted), nodes_to_process.end());
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

    DecisionProcedure::DecisionProcedure(
            const Formula &equalities, AutAssignment init_aut_ass,
            const std::unordered_set<BasicTerm>& init_length_sensitive_vars,
            ast_manager& m, seq_util& m_util_s, arith_util& m_util_a
    ) : prep_handler(equalities, init_aut_ass, init_length_sensitive_vars), m{ m }, m_util_s{ m_util_s },
        m_util_a{ m_util_a },
        init_length_sensitive_vars{ init_length_sensitive_vars },
        formula { equalities },
        init_aut_ass{ init_aut_ass } {
    }

    bool DecisionProcedure::compute_next_solution() {
        // iteratively select next state of solving that can lead to solution and
        // process one of the unprocessed nodes (or possibly find solution)
        while (!worklist.empty()) {
            SolvingState element_to_process = std::move(worklist.front());
            worklist.pop_front();

            if (element_to_process.nodes_to_process.empty()) {
                // we found another solution, element_to_process contain the automata
                // assignment and variable substition that satisfy the original
                // inclusion graph
                solution = std::move(element_to_process);
                return true;
            }

            // we will now process one inclusion from the inclusion graph which is at front
            // i.e. we will update automata assignments and substitutions so that this inclusion is fulfilled
            std::shared_ptr<GraphNode> node_to_process = element_to_process.nodes_to_process.front();
            element_to_process.nodes_to_process.pop_front();
            assert(node_to_process != nullptr);

            STRACE("str", tout << "Processing node with inclusion " << node_to_process->get_predicate() <<std::endl;);
            STRACE("str", tout << "Length variables are:"; 
                          for(auto const &var : node_to_process->get_predicate().get_vars()) {
                              if (element_to_process.length_sensitive_vars.count(var)) {
                                  tout << " " << var.to_string();
                              }
                          }
                          tout << std::endl;
                          );

            const auto &left_side_vars = node_to_process->get_predicate().get_left_side();
            const auto &right_side_vars = node_to_process->get_predicate().get_right_side();

            // this will decide whether we will continue in our search by DFS or by BFS
            bool is_node_to_process_on_cycle = element_to_process.inclusion_graph->is_on_cycle(node_to_process);


            /********************************************************************************************************/
            /****************************************** One side is empty *******************************************/
            /********************************************************************************************************/
            // As kinda opmtimalization step, we do "noodlification" for empty sides separately (i.e. sides that
            // represent empty string). This is because it is simpler, we would get only one noodle so we just need to
            // check that the non-empty side actually contains empty string and replace the vars on that side by epsilon.
            if (right_side_vars.empty() || left_side_vars.empty()) {
                std::unordered_map<BasicTerm, std::vector<BasicTerm>> substitution_map;
                auto const non_empty_side_vars = right_side_vars.empty() ? 
                                                        node_to_process->get_predicate().get_left_set()
                                                      : node_to_process->get_predicate().get_right_set();
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

                // We might be updating left side, in that case we need to process all nodes that contain the variables from the left,
                // i.e. those nodes to which node_to_process goes to. In the case we are updating right side, there will be no edges
                // coming from node_to_process, so this for loop will do nothing.
                for (const auto &node : element_to_process.inclusion_graph->get_edges_from(node_to_process)) {
                    // we push only those nodes which are not already in nodes_to_process
                    // if the node_to_process is on cycle, we need to do BFS
                    // if it is not on cycle, we can do DFS
                    // TODO: can we really do DFS??
                    element_to_process.push_unique(node, is_node_to_process_on_cycle);
                }

                // we need to make a deep copy, because we will be updating this graph
                auto new_node_to_process = element_to_process.make_deep_copy_of_inclusion_graph_only_nodes(node_to_process);
                //remove processed inclusion from the inclusion graph
                element_to_process.inclusion_graph->remove_node(new_node_to_process); // TODO: is this safe?
                // do substitution in the inclusion graph
                element_to_process.substitute_vars(substitution_map);
                // update inclusion graph edges
                element_to_process.inclusion_graph->add_inclusion_graph_edges();
                // update the substitution_map of new_element by the new substitutions
                element_to_process.substitution_map.merge(substitution_map);

                // TODO: should we really push to front when not on cycle?
                // TODO: maybe for this case of one side being empty, we should just push to front?
                if (!is_node_to_process_on_cycle) {
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
                if (is_node_to_process_on_cycle // we do not test inclusion if we have node that is not on cycle, because we will not go back to it (TODO: should we really not test it?)
                    && Mata::Nfa::is_included(element_to_process.aut_ass.get_automaton_concat(left_side_vars), *right_side_automata[0])) {
                    // TODO can I push to front? I think I can, and I probably want to, so I can immediately test if it is not sat (if element_to_process.nodes_to_process is empty), or just to get to sat faster
                    worklist.push_front(element_to_process);
                    // we continue as there is no need for noodlification, inclusion already holds
                    continue;
                }
            }
            /********************************************************************************************************/
            /*************************************** End of inclusion test ******************************************/
            /********************************************************************************************************/


            // We are going to change the automata on the left side (potentially also split some on the right side, but that should not have impact)
            // so we need to add all nodes whose variable assignments are going to change on the right side (i.e. we follow inclusion graph) for processing.
            // Warning: Self-loops are not in inclusion graph, but we might still want to add this node again to nodes_to_process, however, this node will be
            // split during noodlification, so we will only add parts whose right sides actually change (see below in noodlification)
            for (const auto &node : element_to_process.inclusion_graph->get_edges_from(node_to_process)) {
                // we push only those nodes which are not already in nodes_to_process
                // if the node_to_process is on cycle, we need to do BFS
                // if it is not on cycle, we can do DFS
                // TODO: can we really do DFS??
                element_to_process.push_unique(node, is_node_to_process_on_cycle);
            }
            // We will need the set of left vars, so we can sort the 'non-existing self-loop' in noodlification (see previous warning)
            const auto left_vars_set = node_to_process->get_predicate().get_left_set();


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
                SolvingState new_element = element_to_process;
                // we need to make a deep copy, because we will be updating this graph
                // TODO if !is_there_length_on_right we should not copy somehow, if there are no automata accepting only empty word
                auto new_node_to_process = new_element.make_deep_copy_of_inclusion_graph_only_nodes(node_to_process);

                //remove processed inclusion from the inclusion graph
                new_element.inclusion_graph->remove_node(new_node_to_process); // TODO: is this safe?

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
                            const auto &new_inclusion = new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                            // we also add this inclusion to the worklist, as it represents unification
                            // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                            // TODO: is this correct? can we push to the front?
                            // TODO: can't we push to front even if it is on cycle??
                            new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
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
                        const auto &new_inclusion = new_element.inclusion_graph->add_node(right_side_divisions_to_new_vars[i], division);
                        // we add this inclusion to the worklist only if the right side contains something that was on the left (i.e. it was possibly changed)
                        for (const auto &right_var : division) {
                            if (left_vars_set.count(right_var) > 0) {
                                // TODO: again, push to front? back? where the fuck to push??
                                new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
                                break;
                            }
                        }
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
                    if (substitution_map.count(left_var)) {
                        // left_var is already substituted, therefore we add 'left_var ⊆ left_side_vars_to_new_vars[i]' to the inclusion graph
                        std::vector<BasicTerm> new_inclusion_left_side{ left_var };
                        const auto &new_inclusion = new_element.inclusion_graph->add_node(new_inclusion_left_side, left_side_vars_to_new_vars[i]);
                        // we also add this inclusion to the worklist, as it represents unification
                        // we push it to the front if we are processing node that is not on the cycle, because it should not get stuck in the cycle then
                        // TODO: is this correct? can we push to the front?
                        // TODO: can't we push to front even if it is on cycle??
                        new_element.push_unique(new_inclusion, is_node_to_process_on_cycle);
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

            ++noodlification_no; // TODO: when to do this increment?? maybe noodlification_no should be part of SolvingState?
            /********************************************************************************************************/
            /*************************************** End of noodlification ******************************************/
            /********************************************************************************************************/

        }

        // there are no solving states left, which means nothing led to solution -> it must be unsatisfiable
        return false;
    }

    /**
     * @brief Get length formula from the automata assignment @p ass wrt variables @p vars.
     * 
     * @param variable_map Mapping of BasicTerm variables to Z3 expressions
     * @param ass Automata assignment
     * @param vars Set of variables
     * @return expr_ref Length formula
     */
    expr_ref DecisionProcedure::get_length_ass(std::map<BasicTerm, expr_ref>& variable_map, const AutAssignment& ass, const std::unordered_set<smt::noodler::BasicTerm>& vars) {
        expr_ref lengths(this->m.mk_true(), this->m);

        for(const BasicTerm& var :vars) {
            std::set<std::pair<int, int>> aut_constr = Mata::Strings::get_word_lengths(*ass.at(var));

            auto it = variable_map.find(var);
            expr_ref var_expr(this->m);
            if(it != variable_map.end()) { // take the existing variable from the map
                var_expr = it->second;
            } else { // if the variable is not found, it was introduced in the preprocessing -> create a new z3 variable
                var_expr = util::mk_str_var(var.get_name().encode(), this->m, this->m_util_s);
            }
            lengths = this->m.mk_and(lengths, mk_len_aut(var_expr, aut_constr));
        }

        // collect lengths introduced by the preprocessing
        expr_ref prep_formula = util::len_to_expr(
                this->prep_handler.get_len_formula(),
                variable_map,
                this->m, this->m_util_s, this->m_util_a );

        if(!this->m.is_true(prep_formula)) {
            lengths = this->m.mk_and(lengths, prep_formula);
        }

        // check whether disequalities are satisfiable
        if(!check_diseqs(ass)) {
            lengths = this->m.mk_and(lengths, this->m.mk_false());
        }

        STRACE("str", tout << mk_pp(lengths, this->m) << "\n");

        return lengths;
    }

    /**
     * @brief Get length constraints of the solution
     *
     * @param variable_map Mapping of BasicTerm variables to the corresponding z3 variables
     * @return expr_ref Length formula describing all solutions
     */
    expr_ref DecisionProcedure::get_lengths(std::map<BasicTerm, expr_ref>& variable_map) {
        AutAssignment ass;
        if(this->solution.aut_ass.size() == 0) {
            ass = this->init_aut_ass;
            return get_length_ass(variable_map, ass, ass.get_keys());
        } else {
            ass = this->solution.flatten_substition_map();
            return get_length_ass(variable_map, ass, this->init_length_sensitive_vars);
        }
    }

    /**
     * @brief Check that disequalities are satisfiable. Assumed to be called if the
     * decision procedure returns SAT.
     *
     * @param ass SAT automata assignment
     * @return true Disequalities are SAT
     */
    bool DecisionProcedure::check_diseqs(const AutAssignment& ass) {
        for(const auto& pr : this->prep_handler.get_diseq_variables()) {
            auto s1 = Mata::Strings::get_shortest_words(*ass.at(pr.first));
            auto s2 = Mata::Strings::get_shortest_words(*ass.at(pr.second));
            if(s1.size() == 1 && s2.size() == 1 && s1 == s2) {
                return false;
            }
        }
        return true;
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
            // TODO the ordering of nodes_to_process right now is given by how they were added from the splitting graph, should we use something different?
            initialWlEl.inclusion_graph = std::make_shared<Graph>(Graph::create_inclusion_graph(this->formula, initialWlEl.nodes_to_process));
        }

        worklist.push_back(initialWlEl);
    }

    /**
     * @brief Preprocessing.
     */
    void DecisionProcedure::preprocess() {
        // As a first preprocessing operation, convert string literals to fresh variables with automata assignment
        //  representing their string literal.
        conv_str_lits_to_fresh_lits();
        this->prep_handler = FormulaPreprocess(this->formula, this->init_aut_ass, this->init_length_sensitive_vars);

        // So-far just lightweight preprocessing
        this->prep_handler.propagate_variables();
        this->prep_handler.propagate_eps();
        this->prep_handler.remove_regular();
        this->prep_handler.generate_identities();
        this->prep_handler.propagate_variables();
        this->prep_handler.refine_languages();
        this->prep_handler.reduce_diseqalities();
        this->prep_handler.remove_trivial();
        // replace disequalities
        this->prep_handler.replace_disequalities();

        // Refresh the instance
        this->init_aut_ass = this->prep_handler.get_aut_assignment();
        this->init_length_sensitive_vars = this->prep_handler.get_len_variables();
        this->formula = this->prep_handler.get_modified_formula();

        if(this->formula.get_predicates().size() > 0) {
            this->init_aut_ass.reduce(); // reduce all automata in the automata assignment
        }

        STRACE("str", tout << "preprocess-output: " << this->formula.to_string() << "\n" );
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
        expr_ref len_x(this->m_util_s.str.mk_length(var), this->m);
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
        res = expr_ref(this->m.mk_and(res, this->m_util_a.mk_ge(this->m_util_s.str.mk_length(var), this->m_util_a.mk_int(0))), this->m);
        return res;
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
} // Namespace smt::noodler.
