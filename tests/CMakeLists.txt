set(SCRIPT_DIR ${CMAKE_SOURCE_DIR}/scripts)

add_test(
    NAME checkall
    COMMAND bash -c "KATER=$<TARGET_FILE:${PROJECT_NAME}> ${SCRIPT_DIR}/checkall.sh"
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(checkall PROPERTIES LABELS "integration" TIMEOUT 600)

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
