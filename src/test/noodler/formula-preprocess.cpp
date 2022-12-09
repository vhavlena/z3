#include <iostream>

#include <catch2/catch_test_macros.hpp>

#include <smt/theory_str_noodler/inclusion_graph_node.h>
#include <smt/theory_str_noodler/formula_preprocess.h>
#include <smt/theory_str_noodler/theory_str_noodler.h>

using namespace smt::noodler;

TEST_CASE( "Preprocess to strings", "[noodler]" ) {
    auto predicate1{ Predicate(PredicateType::Equation) };

    constexpr auto term_name{ "x_1" };
    auto term{ BasicTerm(BasicTermType::Variable, term_name) };
    auto& left{ predicate1.get_left_side() };
    left.emplace_back(term);
    left.emplace_back( BasicTermType::Literal, "lit" );
    left.emplace_back(term);

    auto term2{ BasicTerm(BasicTermType::Variable, "x_2") };
    auto& right{ predicate1.get_right_side() };
    right.emplace_back(term2);
    right.emplace_back(term2);

    BasicTerm term_lit{ BasicTermType::Literal, "3"};
    BasicTerm term_lit2{ BasicTermType::Literal, "5"};
    BasicTerm term_var{ BasicTermType::Variable, "x_4"};
    BasicTerm term_var2{ BasicTermType::Variable, "x_6"};

    Predicate predicate2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({term_lit, term_var}), std::vector<BasicTerm>({term_lit2, term_var2}) })  );

    Formula conj;
    conj.add_predicate(predicate1);
    conj.add_predicate(predicate2);
    FormulaVar fvar(conj);

    VarNode v1{.term = BasicTerm(BasicTermType::Variable, "x_1"), .eq_index = 0, .position = -1};
    VarNode v2{.term = BasicTerm(BasicTermType::Variable, "x_1"), .eq_index = 0, .position = -1};

    CHECK(v1 == v2);
    INFO(fvar.to_string());
    CHECK(fvar.get_var_positions(predicate1, 0) == std::set<VarNode>({ {.term = BasicTerm(BasicTermType::Variable, "x_1"), .eq_index = 0, .position = -1 }, 
        {.term = BasicTerm(BasicTermType::Variable, "x_1"), .eq_index = 0, .position = -3 }, 
        {.term = BasicTerm(BasicTermType::Variable, "x_2"), .eq_index = 0, .position = 1 }, 
        {.term = BasicTerm(BasicTermType::Variable, "x_2"), .eq_index = 0, .position = 2 } }));
}

TEST_CASE( "Remove regular", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};
    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1}), std::vector<BasicTerm>({x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2, x6, a}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x3, b, x4, b}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x5}), std::vector<BasicTerm>({x4}) })  );

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    conj.add_predicate(eq3);
    conj.add_predicate(eq4);
    FormulaPreprocess prep(conj);
    prep.remove_regular();

    CHECK(prep.get_formula().get_predicate(0) == eq1);
}

TEST_CASE( "Generate identities", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1}), std::vector<BasicTerm>({y1, x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1, b}), std::vector<BasicTerm>({x2, b}) })  );

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    FormulaPreprocess prep(conj);
    prep.generate_identities();
    std::set<Predicate> res;
    res.insert(eq1);
    res.insert(eq2);
    res.insert(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a}), std::vector<BasicTerm>({x1}) })  ));
    res.insert(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  ));
    CHECK(prep.get_formula().get_predicates_set() == res);
}

TEST_CASE( "Replace", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1}), std::vector<BasicTerm>({y1, x1, x1}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2, b}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({y1, b}) })  );
    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );

    Predicate res;
    CHECK(eq1.replace(y1, std::vector<BasicTerm>({y1, a, x1}), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1, a, x1}), std::vector<BasicTerm>({y1, a, x1, x1, x1}) })  ));
    CHECK(eq1.replace(x1, std::vector<BasicTerm>(), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a}), std::vector<BasicTerm>({y1}) })  ));
    CHECK(eq2.replace(x1, std::vector<BasicTerm>(), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>(), std::vector<BasicTerm>({x2, b}) })  ));
    CHECK(!eq2.replace(y1, std::vector<BasicTerm>(), res));
    CHECK(eq4.replace(x2, std::vector<BasicTerm>({x1}), res));
    CHECK(res == Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x1}) })  ));

    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq3);
    FormulaPreprocess prep(conj);
    prep.replace(y1, std::vector<BasicTerm>({y1, a, x1}));
    Formula res_conj;
    res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({y1, a, x1, a, x1}), std::vector<BasicTerm>({y1, a, x1, x1, x1}) })));
    res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({y1, a, x1, b}) })));
    FormulaPreprocess prep_res(res_conj);
    CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
}

TEST_CASE( "Replace 2", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    

    Predicate eq4(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq5(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq6(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Formula conj2;
    conj2.add_predicate(eq4);
    conj2.add_predicate(eq5);
    conj2.add_predicate(eq6);
    FormulaPreprocess prep2(conj2);
    prep2.replace(x2, std::vector<BasicTerm>({x1}));
    prep2.clean_varmap();
    Formula res_conj2;
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x1}) })));
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x1}) })));
    res_conj2.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })));
    FormulaPreprocess prep_res2(res_conj2);
    INFO(prep2.to_string());
    CHECK(prep2.get_formula().get_varmap() == prep_res2.get_formula().get_varmap());
}

TEST_CASE( "Propagate variables", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x2}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    conj.add_predicate(eq3);
    FormulaPreprocess prep(conj);
    
    prep.propagate_variables();
    prep.clean_varmap();
    INFO(prep.to_string());

    Formula res_conj;
    res_conj.add_predicate(Predicate(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x1, x4}), std::vector<BasicTerm>({b, x1, x1}) })));
    FormulaPreprocess prep_res(res_conj);

    
    CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
    CHECK(prep.get_formula().get_predicates_set() == prep_res.get_formula().get_predicates_set());
}

TEST_CASE( "Remove duplicates", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4}), std::vector<BasicTerm>({b, x1, x2}) })  );
    Predicate eq3(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({x1}), std::vector<BasicTerm>({x3}) })  );
    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq3);
    conj.add_predicate(eq2);
    FormulaPreprocess prep(conj);

    Formula res_conj;
    res_conj.add_predicate(eq1);
    res_conj.add_predicate(eq3);
    FormulaPreprocess prep_res(res_conj);

    INFO(prep.to_string());
    INFO(prep_res.to_string());
    CHECK(prep.get_formula().get_varmap() == prep_res.get_formula().get_varmap());
    CHECK(prep.get_formula().get_predicates_set() == prep_res.get_formula().get_predicates_set());
}


TEST_CASE( "Sublists", "[noodler]" ) {
    BasicTerm y1{ BasicTermType::Variable, "y_1"};
    BasicTerm x1{ BasicTermType::Variable, "x_1"};
    BasicTerm x2{ BasicTermType::Variable, "x_2"};
    BasicTerm x3{ BasicTermType::Variable, "x_3"};
    BasicTerm x4{ BasicTermType::Variable, "x_4"};
    BasicTerm x5{ BasicTermType::Variable, "x_5"};
    BasicTerm x6{ BasicTermType::Variable, "x_6"};
    BasicTerm a{ BasicTermType::Literal, "a"};
    BasicTerm b{ BasicTermType::Literal, "b"};    
    Predicate eq1(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({a, x3, x4, b}), std::vector<BasicTerm>({x1, x1, x2}) })  );
    Predicate eq2(PredicateType::Equation, std::vector<std::vector<BasicTerm>>({ std::vector<BasicTerm>({b, x3, x4, b}), std::vector<BasicTerm>({x2, x1, x2}) })  );
    Formula conj;
    conj.add_predicate(eq1);
    conj.add_predicate(eq2);
    FormulaPreprocess prep(conj);
    std::map<Concat, unsigned> res;
    prep.get_regular_sublists(res);
    
    // for(const auto& c : res) {
    //     std::cout << concat_to_string(c.first) << " : " << c.second << std::endl;
    // }

    CHECK(res == std::map<Concat, unsigned>({ {std::vector<BasicTerm>({x3, x4, b}), 2}  }));

}