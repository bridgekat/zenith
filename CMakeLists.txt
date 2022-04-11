cmake_minimum_required (VERSION 3.12...3.22)

project (ApiMu VERSION 0.1 LANGUAGES CXX)


# See: https://stackoverflow.com/questions/56957172/cmake-conditionally-run-cppcheck
option (ENABLE_CODE_ANALYSIS "Run code analysis" OFF)
message (STATUS "ENABLE_CODE_ANALYSIS ${ENABLE_CODE_ANALYSIS}")
if (ENABLE_CODE_ANALYSIS)
  find_program (cppcheck cppcheck)
  message (STATUS "cppcheck ${cppcheck}")
  if (NOT (cppcheck MATCHES "NOTFOUND"))
    # Notes:
    # - unmatchedSuppression needed since not all source files are analyzed simultaneously
    # - unusedFunction needed since not all source files are analyzed simultaneously
    # - template needed to force `warning` into output string, and to make `id` available for suppression
    set (CMAKE_CXX_CPPCHECK "${cppcheck}"
      "--enable=all"
      "--inconclusive"
      "--inline-suppr"
      "--quiet"
      "--suppress=unmatchedSuppression"
      "--suppress=unusedFunction"
      "--template='{file}:{line}: warning: {id} ({severity}): {message}'")
  endif ()
endif (ENABLE_CODE_ANALYSIS)

# See: https://cliutils.gitlab.io/modern-cmake/chapters/features/small.html
include (CheckIPOSupported)
check_ipo_supported (RESULT ipo_supported)
if (ipo_supported)
  message (STATUS "IPO/LTO ENABLED")
endif ()

# Set default compile options
macro (target_default_compile_options TARGET)
  target_compile_features   (${TARGET} PRIVATE cxx_std_20)
  set_target_properties     (${TARGET} PROPERTIES CXX_EXTENSIONS OFF)
  if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-Wall>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-Wextra>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-Wdeprecated>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-Weffc++>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_CONCEPT_CHECKS>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG>")
    target_compile_options  (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG_PEDANTIC>")
  endif ()
endmacro ()

# Add targets
add_executable (testcore
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/proof.cpp
  src/elab/procs.cpp
  src/elab/tableau.cpp
  src/testcore.cpp)
target_default_compile_options  (testcore)
target_include_directories      (testcore PRIVATE src)
if (ipo_supprted)
  set_target_oproperties        (testcore PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif ()

add_executable (testeval
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/parsing/language.cpp
  src/eval/sexpr.cpp
  src/eval/environment.cpp
  src/testeval.cpp)
target_default_compile_options  (testeval)
target_include_directories      (testeval PRIVATE src)
if (ipo_supprted)
  set_target_oproperties        (testeval PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif ()

add_executable (testparsing
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/proof.cpp
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/parsing/language.cpp
  src/mu.cpp
  src/testparsing.cpp)
target_default_compile_options  (testparsing)
target_include_directories      (testparsing PRIVATE src)
if (ipo_supprted)
  set_target_oproperties        (testparsing PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif ()

# See: https://json.nlohmann.me/integration/cmake/#fetchcontent
set (JSON_Install OFF CACHE INTERNAL "")
set (JSON_MultipleHeaders ON)
include (FetchContent)
FetchContent_Declare (nlohmann_json URL https://github.com/nlohmann/json/releases/download/v3.10.5/json.tar.xz)
FetchContent_GetProperties (nlohmann_json)
if (NOT nlohmann_json_POPULATED)
  FetchContent_Populate (nlohmann_json)
  add_subdirectory (${nlohmann_json_SOURCE_DIR} ${nlohmann_json_BINARY_DIR} EXCLUDE_FROM_ALL)
endif ()

# See: https://stackoverflow.com/questions/49768454/whats-the-differences-between-pthread-and-pthread-options-in-cmake
set (THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads)

add_executable (testserver
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/proof.cpp
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/parsing/language.cpp
  src/mu.cpp
  src/server/jsonrpc2.cpp
  src/server/languageserver.cpp
  src/server/lsp.cpp
  src/testserver.cpp)
target_default_compile_options  (testserver)
target_include_directories      (testserver PRIVATE src)
target_link_libraries           (testserver PRIVATE nlohmann_json::nlohmann_json Threads::Threads)
#target_precompile_headers       (testserver PRIVATE ${nlohmann_json_SOURCE_DIR}/single_include/nlohmann/json.hpp)
if (ipo_supprted)
  set_target_oproperties        (testserver PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif ()

