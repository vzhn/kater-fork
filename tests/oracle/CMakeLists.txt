# kater-oracle: Kater's verdicts against a reference semantics (needs Z3)
find_package(Z3 CONFIG QUIET)
if(NOT Z3_FOUND)
  message(STATUS "Z3 not found: kater-oracle will not be built")
  return()
endif()

add_executable(kater-oracle
  Audit.cpp
  Certificate.cpp
  Enumerate.cpp
  Execution.cpp
  Export.cpp
  Extensible.cpp
  GenMC.cpp
  Graph.cpp
  Matrix.cpp
  Reference.cpp
  Search.cpp
  Semantics.cpp
  Transforms.cpp
  main.cpp
)
# ParsingDriver.hpp includes the generated Parser.hpp
target_include_directories(kater-oracle PRIVATE ${PROJECT_BINARY_DIR}/src)
target_link_libraries(kater-oracle PRIVATE kater_lib z3::libz3)

# The builtin theory against GenMC's semantics
add_test(NAME oracle-audit COMMAND kater-oracle audit -n 3)
# The automaton transformations against their contracts
add_test(NAME oracle-transforms COMMAND kater-oracle transforms -n 3 --cases 40 --seed 1)
# Kater proves no assertion of the suite that a small graph refutes
file(GLOB ORACLE_CORRECT ${PROJECT_SOURCE_DIR}/tests/correct/basic/*.kat
  ${PROJECT_SOURCE_DIR}/tests/correct/equivalence/*.kat)
add_test(NAME oracle-check-correct COMMAND kater-oracle check -n 3 ${ORACLE_CORRECT})
# The soundness regressions are false claims: each has a counterexample
file(GLOB ORACLE_SOUNDNESS ${PROJECT_SOURCE_DIR}/tests/wrong/soundness/*.kat)
add_test(NAME oracle-soundness-cases
  COMMAND kater-oracle check -n 4 --refutable ${ORACLE_SOUNDNESS})
set_tests_properties(oracle-audit oracle-transforms oracle-check-correct
  oracle-soundness-cases PROPERTIES LABELS "oracle" TIMEOUT 900)

# What the export of each GenMC model relies on: the Checker's claims (the
# inclusions its extensibility checks decide among them), and that the
# rewritten definitions keep their meaning (LKMM on smaller graphs: at 3
# events, each claim of its coherence check takes minutes)
file(GLOB ORACLE_GENMC_MODELS ${PROJECT_SOURCE_DIR}/kat/*-genmc.kat)
set(ORACLE_EXPORT_MODELS ${ORACLE_GENMC_MODELS})
list(FILTER ORACLE_EXPORT_MODELS EXCLUDE REGEX "lkmm-genmc[.]kat$")
add_test(NAME oracle-export COMMAND kater-oracle export -n 3 -t 300 ${ORACLE_EXPORT_MODELS})
add_test(NAME oracle-export-lkmm
  COMMAND kater-oracle export -n 2 -t 300 ${PROJECT_SOURCE_DIR}/kat/lkmm-genmc.kat)
set_tests_properties(oracle-export oracle-export-lkmm PROPERTIES
  LABELS "oracle" TIMEOUT 1800)

# Each GenMC model is extensible on small graphs, as GenMC's exploration
# needs: an event it may add, into a hole under IMM and LKMM, joins every
# small consistent graph consistently; and, as Kater's extensibility check
# claims, added maximally, when nothing after it accesses its location
# (LKMM, the slowest, on smaller graphs)
set(ORACLE_EXTENSIBLE_MODELS ${ORACLE_GENMC_MODELS})
list(FILTER ORACLE_EXTENSIBLE_MODELS EXCLUDE REGEX "lkmm-genmc[.]kat$")
add_test(NAME oracle-extensible
  COMMAND kater-oracle extensible --maximal -n 3 ${ORACLE_EXTENSIBLE_MODELS})
add_test(NAME oracle-extensible-lkmm
  COMMAND kater-oracle extensible --maximal -n 2 ${PROJECT_SOURCE_DIR}/kat/lkmm-genmc.kat)
set_tests_properties(oracle-extensible oracle-extensible-lkmm PROPERTIES
  LABELS "oracle" TIMEOUT 900)

# Models that are not, at a graph each where the oracle finds an event
# GenMC cannot add (vzhn/kater-fork#33): the two of extensible/, which Kater
# rejects, and IMM and LKMM themselves, on larger graphs; and one where IMM
# can add the event, but not maximally
foreach(m mp mp-acq)
  add_test(NAME oracle-extensible-refuted-${m}
    COMMAND kater-oracle extensible --refutable
      --graph ${CMAKE_CURRENT_SOURCE_DIR}/extensible/${m}.graph
      ${CMAKE_CURRENT_SOURCE_DIR}/extensible/${m}-genmc.kat)
  set_tests_properties(oracle-extensible-refuted-${m} PROPERTIES LABELS "oracle")
endforeach()
foreach(case imm:imm-addr-po lkmm:lkmm-moe)
  string(REPLACE ":" ";" parts ${case})
  list(GET parts 0 model)
  list(GET parts 1 graph)
  add_test(NAME oracle-extensible-refuted-${graph}
    COMMAND kater-oracle extensible --refutable
      --graph ${CMAKE_CURRENT_SOURCE_DIR}/extensible/${graph}.graph
      ${PROJECT_SOURCE_DIR}/kat/${model}-genmc.kat)
  set_tests_properties(oracle-extensible-refuted-${graph} PROPERTIES LABELS "oracle")
endforeach()
add_test(NAME oracle-extensible-maximal-refuted-imm-join
  COMMAND kater-oracle extensible --maximal --refutable
    --graph ${CMAKE_CURRENT_SOURCE_DIR}/extensible/imm-join.graph
    ${PROJECT_SOURCE_DIR}/kat/imm-genmc.kat)
set_tests_properties(oracle-extensible-maximal-refuted-imm-join PROPERTIES LABELS "oracle")

# vzhn/kater-fork#33: Kater's extensibility check rejects the two models of
# extensible/, and their exports fail
foreach(m mp mp-acq)
  add_test(NAME oracle-export-issue-33-${m}
    COMMAND kater-oracle export -n 2 ${CMAKE_CURRENT_SOURCE_DIR}/extensible/${m}-genmc.kat)
  set_tests_properties(oracle-export-issue-33-${m} PROPERTIES LABELS "oracle"
    PASS_REGULAR_EXPRESSION "error: not extensible: a cycle of acyclic")
endforeach()

# Kater's proofs of the suite come with certificates, which check, and the
# letter inclusions they rest on hold
add_test(NAME oracle-certify COMMAND kater-oracle certify -n 3 ${ORACLE_CORRECT})
set_tests_properties(oracle-certify PROPERTIES LABELS "oracle" TIMEOUT 900)

# The certificates of the whole suite, checked by the Lean checker in formal/
# (whose build proves it sound), along with copies that differ in one place:
# it must give each file the verdict checkCertificate gave it
find_program(LAKE lake HINTS $ENV{ELAN_HOME}/bin $ENV{HOME}/.elan/bin)
if(LAKE)
  # elan's lake finds its toolchains through ELAN_HOME, which ctest's
  # environment may lack: give it the elan home lake was found in
  get_filename_component(LAKE_HOME ${LAKE} DIRECTORY)
  get_filename_component(LAKE_HOME ${LAKE_HOME} DIRECTORY)
  if(EXISTS ${LAKE_HOME}/toolchains)
    set(LAKE_ENVIRONMENT ELAN_HOME=${LAKE_HOME})
  endif()
  file(GLOB ORACLE_CORRECT_ALL ${PROJECT_SOURCE_DIR}/tests/correct/*/*.kat)
  set(CERTIFICATES_JSON ${CMAKE_CURRENT_BINARY_DIR}/certificates)
  add_test(NAME formal-certificates-clean
    COMMAND ${CMAKE_COMMAND} -E rm -rf ${CERTIFICATES_JSON})
  add_test(NAME formal-certificates-write
    COMMAND kater-oracle certify -n 1 --json ${CERTIFICATES_JSON} ${ORACLE_CORRECT_ALL})
  add_test(NAME formal-certificates-check
    COMMAND ${LAKE} exe kater-cert-check ${CERTIFICATES_JSON}
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/formal)
  set_tests_properties(formal-certificates-clean PROPERTIES
    FIXTURES_SETUP certificates-clean)
  set_tests_properties(formal-certificates-write PROPERTIES
    FIXTURES_REQUIRED certificates-clean FIXTURES_SETUP certificates-json)
  set_tests_properties(formal-certificates-check PROPERTIES
    FIXTURES_REQUIRED certificates-json ENVIRONMENT "${LAKE_ENVIRONMENT}")
  set_tests_properties(formal-certificates-clean formal-certificates-write
    formal-certificates-check PROPERTIES LABELS "oracle;formal" TIMEOUT 1800)

  # The same for the certificates of the claims the export of each GenMC
  # model rests on, the extensibility check's among them
  set(EXPORT_CERTIFICATES_JSON ${CMAKE_CURRENT_BINARY_DIR}/export-certificates)
  add_test(NAME formal-export-certificates-clean
    COMMAND ${CMAKE_COMMAND} -E rm -rf ${EXPORT_CERTIFICATES_JSON})
  add_test(NAME formal-export-certificates-write
    COMMAND kater-oracle export -n 1 --json ${EXPORT_CERTIFICATES_JSON} ${ORACLE_GENMC_MODELS})
  add_test(NAME formal-export-certificates-check
    COMMAND ${LAKE} exe kater-cert-check ${EXPORT_CERTIFICATES_JSON}
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/formal)
  set_tests_properties(formal-export-certificates-clean PROPERTIES
    FIXTURES_SETUP export-certificates-clean)
  set_tests_properties(formal-export-certificates-write PROPERTIES
    FIXTURES_REQUIRED export-certificates-clean FIXTURES_SETUP export-certificates-json)
  set_tests_properties(formal-export-certificates-check PROPERTIES
    FIXTURES_REQUIRED export-certificates-json ENVIRONMENT "${LAKE_ENVIRONMENT}")
  set_tests_properties(formal-export-certificates-clean formal-export-certificates-write
    formal-export-certificates-check PROPERTIES LABELS "oracle;formal" TIMEOUT 1800)
  # One lake at a time in formal/
  set_tests_properties(formal-certificates-check formal-export-certificates-check
    PROPERTIES RESOURCE_LOCK formal-lake)
endif()

# The exported checkers, run inside GenMC, against the reference semantics
# (needs GenMC)
add_subdirectory(genmc)
