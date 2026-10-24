# kater-oracle-runner: the GenMC checkers Kater exports, run on the graphs
# `kater-oracle genmc` hands it (needs a GenMC source tree; its core library
# is built here, without LLVM)
set(GENMC_SOURCE_DIR "$ENV{GENMC_SOURCE_DIR}" CACHE PATH
  "A GenMC source tree, to run the exported checkers in")
if(NOT EXISTS "${GENMC_SOURCE_DIR}/genmc/genmc/Execution/ExecutionGraph.hpp")
  message(STATUS "GenMC not found (GENMC_SOURCE_DIR): the exported checkers will not be run")
  return()
endif()
message(STATUS "Running the exported checkers in GenMC from ${GENMC_SOURCE_DIR}")

include(ExternalProject)
set(GENMC_BUILD_DIR ${CMAKE_CURRENT_BINARY_DIR}/genmc-build)
set(GENMC_LIB ${GENMC_BUILD_DIR}/genmc/libgenmc_lib.a)
ExternalProject_Add(genmc-core
  SOURCE_DIR ${GENMC_SOURCE_DIR}
  BINARY_DIR ${GENMC_BUILD_DIR}
  CMAKE_ARGS -DCMAKE_BUILD_TYPE=Release -DBUILD_LLI=OFF -DBUILD_PASSES=OFF
    -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
  BUILD_COMMAND ${CMAKE_COMMAND} --build . --target genmc_lib
  BUILD_ALWAYS ON
  INSTALL_COMMAND ""
  BUILD_BYPRODUCTS ${GENMC_LIB})

# The checkers, exported from kat/NAME-genmc.kat as ORACLE<NAME>Checker, and
# ORACLE<NAME>Clauses, which gives the verdicts of their error and warning
# clauses too
set(GENMC_MODELS sc tso ra rc11 imm lkmm)
set(CHECKER_DIR ${CMAKE_CURRENT_BINARY_DIR}/checkers)
file(MAKE_DIRECTORY ${CHECKER_DIR})
set(CHECKER_SOURCES)
set(CHECKER_INCLUDES "")
set(CHECKER_TABLE "")
foreach(m ${GENMC_MODELS})
  string(TOUPPER ${m} M)
  set(class ORACLE${M}Checker)
  set(clauses ORACLE${M}Clauses)
  add_custom_command(
    OUTPUT ${CHECKER_DIR}/${class}.cpp ${CHECKER_DIR}/${class}.hpp
    COMMAND sh -c "\"$0\" -e -n oracle${m} -p \"$1\" \"$2\" > \"$1/${m}.log\" 2>&1"
      $<TARGET_FILE:kater> ${CHECKER_DIR} ${PROJECT_SOURCE_DIR}/kat/${m}-genmc.kat
    DEPENDS kater ${PROJECT_SOURCE_DIR}/kat/${m}-genmc.kat
    COMMENT "Exporting the GenMC checker of ${m}"
    VERBATIM)
  add_custom_command(
    OUTPUT ${CHECKER_DIR}/${clauses}.hpp
    COMMAND ${CMAKE_COMMAND} -DHEADER=${CHECKER_DIR}/${class}.hpp -DBASE=${class}
      -DCLASS=${clauses} -DOUT=${CHECKER_DIR}/${clauses}.hpp
      -P ${CMAKE_CURRENT_SOURCE_DIR}/Clauses.cmake
    DEPENDS ${CHECKER_DIR}/${class}.hpp ${CMAKE_CURRENT_SOURCE_DIR}/Clauses.cmake
    COMMENT "Listing the error and warning clauses of ${m}"
    VERBATIM)
  list(APPEND CHECKER_SOURCES ${CHECKER_DIR}/${class}.cpp ${CHECKER_DIR}/${clauses}.hpp)
  string(APPEND CHECKER_INCLUDES "#include \"${clauses}.hpp\"\n")
  string(APPEND CHECKER_TABLE "\t{\"${m}\", [](const Config *c) -> std::unique_ptr<ConsistencyChecker> { return std::make_unique<${clauses}>(c); }},\n")
endforeach()
file(WRITE ${CHECKER_DIR}/Checkers.inc.new
  "${CHECKER_INCLUDES}\n"
  "static const std::pair<const char *, std::unique_ptr<ConsistencyChecker> (*)(const Config *)> CHECKERS[] = {\n"
  "${CHECKER_TABLE}};\n")
configure_file(${CHECKER_DIR}/Checkers.inc.new ${CHECKER_DIR}/Checkers.inc COPYONLY)

find_package(Threads REQUIRED)
find_library(HWLOC_LIBRARY hwloc)
add_executable(kater-oracle-runner Runner.cpp ../Execution.cpp ${CHECKER_SOURCES})
add_dependencies(kater-oracle-runner genmc-core)
target_include_directories(kater-oracle-runner PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_SOURCE_DIR}/.. ${CHECKER_DIR}
  ${GENMC_SOURCE_DIR}/genmc ${GENMC_BUILD_DIR}/include)
target_compile_features(kater-oracle-runner PRIVATE cxx_std_23)
target_compile_definitions(kater-oracle-runner PRIVATE EMIT_NA_LABELS=1)
target_link_libraries(kater-oracle-runner PRIVATE ${GENMC_LIB} Threads::Threads)
if(HWLOC_LIBRARY)
  target_link_libraries(kater-oracle-runner PRIVATE ${HWLOC_LIBRARY})
endif()

# Every graph up to a few events, every one with a heap up to three, and
# random larger ones, for each model: the checker's verdicts against the
# reference semantics, its memory-error checks included (one or two minutes
# each; doc/verification.md has the longer runs)
set(GENMC_TEST_ARGS_sc -n 4 --heap-events 3 --random 3000)
set(GENMC_TEST_ARGS_tso -n 3 --heap-events 3 --random 5000)
set(GENMC_TEST_ARGS_ra -n 3 --heap-events 3 --random 5000)
set(GENMC_TEST_ARGS_rc11 -n 3 --heap-events 3 --random 3000)
set(GENMC_TEST_ARGS_imm -n 3 --heap-events 3 --random 2000)
set(GENMC_TEST_ARGS_lkmm -n 2 --heap-events 3 --random 2000)
foreach(m ${GENMC_MODELS})
  add_test(NAME oracle-genmc-${m}
    COMMAND kater-oracle genmc --runner $<TARGET_FILE:kater-oracle-runner>
      ${GENMC_TEST_ARGS_${m}} ${PROJECT_SOURCE_DIR}/kat/${m}-genmc.kat)
  set_tests_properties(oracle-genmc-${m} PROPERTIES LABELS "oracle;genmc" TIMEOUT 1800)
endforeach()

# vzhn/kater-fork#27: the acyclicity checks can miss a cycle, depending on
# the order they explore labels in. This passes while GenMC still accepts
# the graph; once fixed, it fails: then expect the graph to agree instead
add_test(NAME oracle-genmc-issue-27
  COMMAND kater-oracle genmc --runner $<TARGET_FILE:kater-oracle-runner>
    --graph ${CMAKE_CURRENT_SOURCE_DIR}/graphs/issue-27.graph
    ${PROJECT_SOURCE_DIR}/kat/imm-genmc.kat)
set_tests_properties(oracle-genmc-issue-27 PROPERTIES LABELS "oracle;genmc"
  PASS_REGULAR_EXPRESSION "DISAGREE isConsistent\\(G\\): GenMC says true")

