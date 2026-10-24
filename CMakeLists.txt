cmake_minimum_required(VERSION 3.15...3.28)
project(kater VERSION 0.4.0 LANGUAGES CXX)

enable_testing()
include(CTest)

include(GNUInstallDirs)

# Always emit compile_commands.json
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# clang-tidy integration
option(TIDY "Run clang-tidy")
if(TIDY)
  find_program(CLANG_TIDY clang-tidy REQUIRED)
  set(CMAKE_CXX_CLANG_TIDY
    clang-tidy;
    -header-filter=.*;
    -config-file=${CMAKE_SOURCE_DIR}/.clang-tidy
  )
endif()

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
add_subdirectory(src)

# formal/ proves in Lean what mirrors parts of the C++. With no CI to run the
# ctest check-mirrors, every build warns when one of those parts changed
# since formal/ was last reviewed against it, and goes on
add_custom_target(mirrors-warning ALL
  COMMAND ${CMAKE_SOURCE_DIR}/scripts/check-mirrors.sh --warn
  VERBATIM)
add_dependencies(mirrors-warning ${PROJECT_NAME})

option(BUILD_TESTS "Enable test building" OFF)
if(BUILD_TESTS)
add_subdirectory(tests)
endif()
