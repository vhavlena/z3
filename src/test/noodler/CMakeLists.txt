find_package(Catch2 3 REQUIRED)

# These tests can use the Catch2-provided main
z3_add_component(noodler
    EXCLUDE_FROM_ALL
    NOT_LIBZ3_COMPONENT # Don't put this component inside libz3
    SOURCES
        inclusion-graph-node.cc
    COMPONENT_DEPENDENCIES
        smt
)

add_executable(test-noodler
        main.cc
)
target_link_libraries(test-noodler PRIVATE Catch2::Catch2WithMain)
z3_add_install_tactic_rule(noodler)
z3_add_memory_initializer_rule(noodler)
z3_add_gparams_register_modules_rule(noodler)
target_compile_definitions(test-noodler PRIVATE ${Z3_COMPONENT_CXX_DEFINES})
target_compile_options(test-noodler PRIVATE ${Z3_COMPONENT_CXX_FLAGS})
target_link_libraries(test-noodler PRIVATE noodler)
target_include_directories(test-noodler PRIVATE ${Z3_COMPONENT_EXTRA_INCLUDE_DIRS})
z3_append_linker_flag_list_to_target(test-noodler ${Z3_DEPENDENT_EXTRA_CXX_LINK_FLAGS})
z3_add_component_dependencies_to_target(test-noodler noodler)


# These tests need their own main
#add_executable(custom-main-tests test.cpp test-main.cpp)
#target_link_libraries(custom-main-tests PRIVATE Catch2::Catch2)
