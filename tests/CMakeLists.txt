set(SCRIPT_DIR ${CMAKE_SOURCE_DIR}/scripts)

add_test(
    NAME checkall
    COMMAND bash -c "KATER=$<TARGET_FILE:${PROJECT_NAME}> ${SCRIPT_DIR}/checkall.sh"
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(checkall PROPERTIES LABELS "integration" TIMEOUT 600)

# No layer may include a header from a layer above it (see src/CMakeLists.txt)
add_test(
    NAME check-layers
    COMMAND ${SCRIPT_DIR}/check-layers.sh
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
)
set_tests_properties(check-layers PROPERTIES LABELS "lint")

# Unit tests
add_subdirectory(unit)

# Kater against a reference semantics (needs Z3)
add_subdirectory(oracle)
