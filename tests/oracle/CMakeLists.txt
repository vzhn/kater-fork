# kater-oracle: Kater's verdicts against a reference semantics (needs Z3)
find_package(Z3 CONFIG QUIET)
if(NOT Z3_FOUND)
  message(STATUS "Z3 not found: kater-oracle will not be built")
  return()
endif()

add_executable(kater-oracle
  Audit.cpp
  Certificate.cpp
  Execution.cpp
  Export.cpp
  Graph.cpp
  Matrix.cpp
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

# What the export of each GenMC model relies on: the Checker's claims, and
# that the rewritten definitions keep their meaning
file(GLOB ORACLE_GENMC_MODELS ${PROJECT_SOURCE_DIR}/kat/*-genmc.kat)
add_test(NAME oracle-export COMMAND kater-oracle export -n 3 ${ORACLE_GENMC_MODELS})
set_tests_properties(oracle-export PROPERTIES LABELS "oracle" TIMEOUT 900)

# Kater's proofs of the suite come with certificates, which check, and the
# letter inclusions they rest on hold
add_test(NAME oracle-certify COMMAND kater-oracle certify -n 3 ${ORACLE_CORRECT})
set_tests_properties(oracle-certify PROPERTIES LABELS "oracle" TIMEOUT 900)
