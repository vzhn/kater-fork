# Kater is built as a stack of layers, each a static library that may only
# depend on the layers below it (scripts/check-layers.sh enforces this on
# the #include graph). From the bottom:
#
#   support   command line, diagnostics, logging, generic containers
#   theory    relations, predicates, and the structural facts about them
#   automata  NFAs over relation/predicate labels and their operations
#   lang      the .kat language: expressions, constraints, modules, parser
#   decision  saturation and the inclusion check (the decision procedure)
#   export    GenMC code generation
#
# The theory, automata and decision layers are the trusted core: a "holds"
# verdict is only as sound as they are. The others cannot affect it.

set(SUPPORT_SOURCES
  Config.cpp
  DbgInfo.cpp
  Error.cpp
  Logger.cpp
)

set(THEORY_SOURCES
  Predicate.cpp
  Relation.cpp
  Theory.cpp
  TransLabel.cpp
)

set(AUTOMATA_SOURCES
  Counterexample.cpp
  NFA.cpp
  NFAUtils.cpp
  Utils.cpp
)

set(LANG_SOURCES
  Assumptions.cpp
  Builtins.cpp
  Constraint.cpp
  KatModule.cpp
  ParsingDriver.cpp
  RegExp.cpp
)

set(DECISION_SOURCES
  Checker.cpp
  Saturation.cpp
)

set(EXPORT_SOURCES
  Exporter.cpp
  GenMCPrinter.cpp
  Printer.cpp
)

# need bison and flex
find_package(FLEX 2.6 REQUIRED)
find_package(BISON 3.2 REQUIRED)

# generate flex/bison sources out of source (clean git; helpful for linting)
flex_target(LEXER Lexer.lpp ${CMAKE_CURRENT_BINARY_DIR}/Lexer.cpp)
bison_target(PARSER Parser.ypp ${CMAKE_CURRENT_BINARY_DIR}/Parser.cpp
  DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/Parser.hpp)
add_flex_bison_dependency(LEXER PARSER)

# link with TBB if present
find_package(TBB)

# the logger serializes concurrent diagnostics with a mutex
find_package(Threads REQUIRED)

# Settings shared by every layer
add_library(kater_common INTERFACE)
target_include_directories(kater_common INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
target_compile_features(kater_common INTERFACE cxx_std_23)

option(KATER_DEBUG "Enable kater debugging infrastructure (ON for Debug)" OFF)
target_compile_definitions(kater_common
  INTERFACE
   $<$<OR:$<CONFIG:Debug>,$<BOOL:${KATER_DEBUG}>>:ENABLE_KATER_DEBUG>
)

add_library(kater_support STATIC ${SUPPORT_SOURCES})
target_link_libraries(kater_support PUBLIC kater_common PRIVATE Threads::Threads)

add_library(kater_theory STATIC ${THEORY_SOURCES})
target_link_libraries(kater_theory PUBLIC kater_support)

add_library(kater_automata STATIC ${AUTOMATA_SOURCES})
target_link_libraries(kater_automata PUBLIC kater_theory)

add_library(kater_lang STATIC ${LANG_SOURCES} ${BISON_PARSER_OUTPUTS} ${FLEX_LEXER_OUTPUTS})
target_include_directories(kater_lang
  PRIVATE ${CMAKE_CURRENT_BINARY_DIR}) # generated files include handwritten
target_link_libraries(kater_lang PUBLIC kater_automata PRIVATE ${FLEX_LIBRARIES})

add_library(kater_decision STATIC ${DECISION_SOURCES})
target_link_libraries(kater_decision PUBLIC kater_lang)
if(TBB_FOUND)
  target_link_libraries(kater_decision PRIVATE TBB::tbb)
else()
  message(TBB not found. Assertion parallelization disabled.)
endif()

add_library(kater_export STATIC ${EXPORT_SOURCES})
target_link_libraries(kater_export PUBLIC kater_decision)

# Everything together, for the executable and the tests
add_library(kater_lib INTERFACE)
target_link_libraries(kater_lib INTERFACE kater_export)

add_executable(${PROJECT_NAME} main.cpp)
target_include_directories(${PROJECT_NAME} PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
target_link_libraries(${PROJECT_NAME} PRIVATE kater_lib)

install(TARGETS ${PROJECT_NAME} RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})
