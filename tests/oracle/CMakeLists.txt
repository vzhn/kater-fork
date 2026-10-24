# kater-oracle: Kater's verdicts against a reference semantics (needs Z3)
find_package(Z3 CONFIG QUIET)
if(NOT Z3_FOUND)
  message(STATUS "Z3 not found: kater-oracle will not be built")
  return()
endif()

add_executable(kater-oracle
  Audit.cpp
  Certificate.cpp
  Chain.cpp
  Enumerate.cpp
  Evidence.cpp
  Execution.cpp
  Export.cpp
  Extensible.cpp
  GenMC.cpp
  Graph.cpp
  GraphJSON.cpp
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

# vzhn/kater-fork#46: the model of extensible/mp-genmc.kat with assumptions
# every graph meets, which made the theory take the checks of an event GenMC
# adds for incompatible ones: the oracle refutes it at mp.graph, and Kater
# rejects it
add_test(NAME oracle-extensible-refuted-mp-incompat
  COMMAND kater-oracle extensible --refutable
    --graph ${CMAKE_CURRENT_SOURCE_DIR}/extensible/mp.graph
    ${CMAKE_CURRENT_SOURCE_DIR}/extensible/mp-incompat-genmc.kat)
add_test(NAME oracle-export-issue-46
  COMMAND kater-oracle export -n 2 ${CMAKE_CURRENT_SOURCE_DIR}/extensible/mp-incompat-genmc.kat)
set_tests_properties(oracle-export-issue-46 PROPERTIES
  PASS_REGULAR_EXPRESSION "error: not extensible: a cycle of acyclic")
set_tests_properties(oracle-extensible-refuted-mp-incompat oracle-export-issue-46 PROPERTIES
  LABELS "oracle")

# Kater's proofs of the suite come with certificates and chains, which
# check, and the letter inclusions and hypotheses they rest on hold
add_test(NAME oracle-certify COMMAND kater-oracle certify -n 3 ${ORACLE_CORRECT})
set_tests_properties(oracle-certify PROPERTIES LABELS "oracle" TIMEOUT 900)

# The certificates of the whole suite, with the chains of passes their right
# automata came by, checked by the Lean checker in formal/ (whose build
# proves it sound), along with copies that differ in one place: it must give
# each file the verdict checkCertificateAndChain gave it, and check chains
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
    FIXTURES_REQUIRED certificates-json ENVIRONMENT "${LAKE_ENVIRONMENT}"
    FAIL_REGULAR_EXPRESSION "\n0 valid certificates with chains")
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
    FIXTURES_REQUIRED export-certificates-json ENVIRONMENT "${LAKE_ENVIRONMENT}"
    FAIL_REGULAR_EXPRESSION "\n0 valid certificates with chains")
  set_tests_properties(formal-export-certificates-clean formal-export-certificates-write
    formal-export-certificates-check PROPERTIES LABELS "oracle;formal" TIMEOUT 1800)

  # The evidence of every step of Kater's proofs of the suite, from each
  # assertion's expressions to its verdict, checked by the Lean checker of
  # whole proofs in formal/, whose build proves that the assertion of
  # evidence it accepts holds on every execution graph where the module's
  # assumptions do
  set(EVIDENCE_JSON ${CMAKE_CURRENT_BINARY_DIR}/evidence)
  add_test(NAME formal-evidence-clean
    COMMAND ${CMAKE_COMMAND} -E rm -rf ${EVIDENCE_JSON})
  add_test(NAME formal-evidence-write
    COMMAND kater-oracle evidence --json ${EVIDENCE_JSON} ${ORACLE_CORRECT_ALL})
  add_test(NAME formal-evidence-check
    COMMAND ${LAKE} exe kater-chain-check ${EVIDENCE_JSON}
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/formal)
  set_tests_properties(formal-evidence-clean PROPERTIES FIXTURES_SETUP evidence-clean)
  set_tests_properties(formal-evidence-write PROPERTIES
    FIXTURES_REQUIRED evidence-clean FIXTURES_SETUP evidence-json)
  set_tests_properties(formal-evidence-check PROPERTIES
    FIXTURES_REQUIRED evidence-json ENVIRONMENT "${LAKE_ENVIRONMENT}"
    FAIL_REGULAR_EXPRESSION "(^|\n)0 assertions accepted")
  set_tests_properties(formal-evidence-clean formal-evidence-write formal-evidence-check
    PROPERTIES LABELS "oracle;formal" TIMEOUT 1800)

  # The same for every claim the export of each GenMC model rests on: the
  # inclusions the Checker proves on the way, and each extensibility check,
  # from the constraint's automaton to the certificates of its words; the
  # build proves that an accepted check makes the export's constraint
  # extensible in the model
  set(EXPORT_EVIDENCE_JSON ${CMAKE_CURRENT_BINARY_DIR}/export-evidence)
  add_test(NAME formal-export-evidence-clean
    COMMAND ${CMAKE_COMMAND} -E rm -rf ${EXPORT_EVIDENCE_JSON})
  add_test(NAME formal-export-evidence-write
    COMMAND kater-oracle evidence --export --json ${EXPORT_EVIDENCE_JSON} ${ORACLE_GENMC_MODELS})
  add_test(NAME formal-export-evidence-check
    COMMAND ${LAKE} exe kater-chain-check ${EXPORT_EVIDENCE_JSON}
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/formal)
  set_tests_properties(formal-export-evidence-clean PROPERTIES
    FIXTURES_SETUP export-evidence-clean)
  set_tests_properties(formal-export-evidence-write PROPERTIES
    FIXTURES_REQUIRED export-evidence-clean FIXTURES_SETUP export-evidence-json)
  set_tests_properties(formal-export-evidence-check PROPERTIES
    FIXTURES_REQUIRED export-evidence-json ENVIRONMENT "${LAKE_ENVIRONMENT}"
    FAIL_REGULAR_EXPRESSION "(^|\n)0 assertions accepted|, 0 extensibility checks accepted")
  set_tests_properties(formal-export-evidence-clean formal-export-evidence-write
    formal-export-evidence-check PROPERTIES LABELS "oracle;formal" TIMEOUT 1800)

  # The model of formal/ against the oracle's semantics, which implement the
  # same reference semantics independently: on every graph up to 3 events (of
  # accesses, fences and dependencies; of the other kinds of events; of a
  # heap), on random graphs with thread events and method calls, on models
  # of the symbolic graph's axioms and on the graph files here, the meaning
  # of each builtin is the same in both, and each graph satisfies the
  # model's axioms
  file(GLOB_RECURSE ORACLE_GRAPH_FILES ${CMAKE_CURRENT_SOURCE_DIR}/*.graph)
  list(SORT ORACLE_GRAPH_FILES)
  set(ORACLE_GRAPH_ARGS)
  foreach(f ${ORACLE_GRAPH_FILES})
    list(APPEND ORACLE_GRAPH_ARGS --graph ${f})
  endforeach()
  set(MODEL_JSON ${CMAKE_CURRENT_BINARY_DIR}/model-graphs.jsonl)
  add_test(NAME formal-model-write
    COMMAND kater-oracle graphs --json ${MODEL_JSON} -n 3 --heap-events 3 --random 2000
      --symbolic 300 --seed 1 ${ORACLE_GRAPH_ARGS})
  add_test(NAME formal-model-check
    COMMAND ${LAKE} exe kater-model-check ${MODEL_JSON}
    WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}/formal)
  set_tests_properties(formal-model-write PROPERTIES FIXTURES_SETUP model-json)
  set_tests_properties(formal-model-check PROPERTIES
    FIXTURES_REQUIRED model-json ENVIRONMENT "${LAKE_ENVIRONMENT}")
  set_tests_properties(formal-model-write formal-model-check PROPERTIES
    LABELS "oracle;formal" TIMEOUT 1800)

  # One lake at a time in formal/
  set_tests_properties(formal-certificates-check formal-export-certificates-check
    formal-evidence-check formal-export-evidence-check formal-model-check
    PROPERTIES RESOURCE_LOCK formal-lake)
endif()

# The exported checkers, run inside GenMC, against the reference semantics
# (needs GenMC)
add_subdirectory(genmc)
