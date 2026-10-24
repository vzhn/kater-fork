set(SCRIPT_DIR ${CMAKE_SOURCE_DIR}/scripts)

add_test(
    NAME checkall
    COMMAND bash -c "KATER=$<TARGET_FILE:${PROJECT_NAME}> ${SCRIPT_DIR}/checkall.sh"
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(checkall PROPERTIES LABELS "integration" TIMEOUT 600)

# kat/imm-genmc.kat and kat/lkmm-genmc.kat are not extensible
# (vzhn/kater-fork#38, #39): they say so with export nonextensible, and
# export with a warning. Once a model is, its test fails: drop the flag
foreach(m imm lkmm)
  add_test(NAME export-nonextensible-${m}
    COMMAND $<TARGET_FILE:${PROJECT_NAME}> -e ${CMAKE_SOURCE_DIR}/kat/${m}-genmc.kat)
  set_tests_properties(export-nonextensible-${m} PROPERTIES LABELS "integration"
    PASS_REGULAR_EXPRESSION "warning: not extensible")
endforeach()

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
