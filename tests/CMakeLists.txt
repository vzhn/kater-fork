set(SCRIPT_DIR ${CMAKE_SOURCE_DIR}/scripts)

add_test(
    NAME checkall
    COMMAND bash -c "KATER=$<TARGET_FILE:${PROJECT_NAME}> ${SCRIPT_DIR}/checkall.sh"
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(checkall PROPERTIES LABELS "integration" TIMEOUT 600)

# vzhn/kater-fork#37: a counterexample has the whole word, the path after the
# letter the right-hand side cannot read included
add_test(
    NAME counterexample-issue-37
    COMMAND $<TARGET_FILE:${PROJECT_NAME}>
      ${CMAKE_CURRENT_SOURCE_DIR}/wrong/basic/counterexample-completion.kat
)
set_tests_properties(counterexample-issue-37 PROPERTIES LABELS "integration"
    PASS_REGULAR_EXPRESSION "counterexample: \\[R\\] po \\[W\\] rf ===> \\[R\\] po \\[F\\] ?\n")

# Every GenMC model exports (vzhn/kater-fork#35: with assertions on, Kater
# aborted on all of them)
foreach(m sc tso ra rc11 imm lkmm)
  add_test(
      NAME export-${m}-genmc
      COMMAND sh -c "mkdir -p \"$1\" && \"$0\" -e -n test${m} -p \"$1\" \"$2\""
        $<TARGET_FILE:${PROJECT_NAME}> ${CMAKE_CURRENT_BINARY_DIR}/export/${m}
        ${CMAKE_SOURCE_DIR}/kat/${m}-genmc.kat
  )
  set_tests_properties(export-${m}-genmc PROPERTIES LABELS "integration" TIMEOUT 600)
endforeach()

# kat/imm-genmc.kat and kat/lkmm-genmc.kat are not extensible
# (vzhn/kater-fork#38, #39): they say so with export nonextensible, and
# export with a warning. Once a model is, its test fails: drop the flag
foreach(m imm lkmm)
  add_test(NAME export-nonextensible-${m}
    COMMAND $<TARGET_FILE:${PROJECT_NAME}> -e ${CMAKE_SOURCE_DIR}/kat/${m}-genmc.kat)
  set_tests_properties(export-nonextensible-${m} PROPERTIES LABELS "integration"
    PASS_REGULAR_EXPRESSION "warning: not extensible")
endforeach()

# vzhn/kater-fork#38: an extra export is printed for the newest event and
# for the whole graph, both const
add_test(NAME export-extra
  COMMAND $<TARGET_FILE:${PROJECT_NAME}> -e ${CMAKE_CURRENT_SOURCE_DIR}/export/extra-genmc.kat)
set_tests_properties(export-extra PROPERTIES LABELS "integration"
  PASS_REGULAR_EXPRESSION "bool scFull\\(const EventLabel \\*lab\\) const [^\n]*\n[^\n]*bool scFull\\(const ExecutionGraph &g\\) const")

# vzhn/kater-fork#51: the check of A <= VIEW, for an A that accepts nothing,
# ended without a return. Every function of the exported checker that
# returns a value has to end with one
add_test(
    NAME export-issue-51
    COMMAND sh -c "mkdir -p \"$1\" && \"$0\" -e -n issue51 -p \"$1\" \"$2\" && \"$3\" \"$1/ISSUE51Checker.cpp\""
      $<TARGET_FILE:${PROJECT_NAME}> ${CMAKE_CURRENT_BINARY_DIR}/export/issue-51
      ${CMAKE_CURRENT_SOURCE_DIR}/export/empty-in-view-genmc.kat ${SCRIPT_DIR}/check-returns.sh
)
set_tests_properties(export-issue-51 PROPERTIES LABELS "integration")

# No layer may include a header from a layer above it (see src/CMakeLists.txt)
add_test(
    NAME check-layers
    COMMAND ${SCRIPT_DIR}/check-layers.sh
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(check-layers PROPERTIES LABELS "lint")

# The C++ that formal/ mirrors in Lean has not changed since its last review
add_test(
    NAME check-mirrors
    COMMAND ${SCRIPT_DIR}/check-mirrors.sh
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(check-mirrors PROPERTIES LABELS "lint;formal")

# Unit tests
add_subdirectory(unit)

# Kater against a reference semantics (needs Z3)
add_subdirectory(oracle)
