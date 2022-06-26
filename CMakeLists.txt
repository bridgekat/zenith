cmake_minimum_required (VERSION 3.12...3.22)

project (ApiMu VERSION 0.1 LANGUAGES CXX)

option (APIMU_ENABLE_CODE_ANALYSIS "Run code analysis with cppcheck" OFF)
option (APIMU_ENABLE_MOST_WARNINGS "Enable most warnings" OFF)
option (APIMU_ENABLE_WARNINGS_AS_ERRORS "Treat warnings as errors" OFF)
option (APIMU_ENABLE_GLIBCXX_DEBUG_CHECKS "Enable GLIBCXX debug checks at debug configuration" ON)
option (APIMU_ENABLE_ASAN "Enable ASan (MSVC/GCC/Clang)" OFF)
option (APIMU_ENABLE_UBSAN "Enable UBSan (GCC/Clang)" OFF)
option (APIMU_LD_EXTEND_STACK "Extend stack memory to 10MB (Linux LD)" OFF)
option (APIMU_MACOS_LD_EXTEND_STACK "Extend stack memory to 10MB (macOS LD)" OFF)
option (APIMU_LINK_EXTEND_STACK "Extend stack memory to 10MB (MSVC LINK)" OFF)

# See: https://cliutils.gitlab.io/modern-cmake/chapters/features/small.html
include (CheckIPOSupported)
check_ipo_supported (RESULT IPO_SUPPORTED)
if (IPO_SUPPORTED)
  message (STATUS "IPO/LTO ENABLED")
endif ()

# See: https://stackoverflow.com/questions/56957172/cmake-conditionally-run-cppcheck
if (APIMU_ENABLE_CODE_ANALYSIS)
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
endif ()

# Set default compile options
macro (target_default_compile_options TARGET)
  target_compile_features     (${TARGET} PRIVATE cxx_std_20)
  set_target_properties       (${TARGET} PROPERTIES CXX_EXTENSIONS OFF)
  if (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
    target_compile_options    (${TARGET} PRIVATE "/MP" "/EHsc")
  endif ()
  if (APIMU_ENABLE_MOST_WARNINGS)
    if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
      target_compile_options  (${TARGET} PRIVATE "-Wall" "-Wextra" "-Wdeprecated")
      target_compile_options  (${TARGET} PRIVATE "-Weffc++")
    elseif (CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
      target_compile_options  (${TARGET} PRIVATE "-Wall" "-Wextra")
    elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
      target_compile_options  (${TARGET} PRIVATE "/W4" "/permissive-")
    endif ()
  endif ()
  if (APIMU_ENABLE_WARNINGS_AS_ERRORS)
    if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
      target_compile_options  (${TARGET} PRIVATE "-Werror")
    elseif (CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
      target_compile_options  (${TARGET} PRIVATE "-Werror")
    elseif (CMAKE_CXX_COMPILER_ID STREQUAL "MSVC")
      target_compile_options  (${TARGET} PRIVATE "/WX")
    endif ()
  endif ()
  if (APIMU_ENABLE_GLIBCXX_DEBUG_CHECKS)
    target_compile_options    (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_CONCEPT_CHECKS>")
    target_compile_options    (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG>")
    target_compile_options    (${TARGET} PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG_PEDANTIC>")
  endif ()
  if (APIMU_ENABLE_ASAN)
    target_compile_options    (${TARGET} PRIVATE "-fsanitize=address")
  endif ()
  if (APIMU_ENABLE_UBSAN)
    target_compile_options    (${TARGET} PRIVATE "-fsanitize=undefined")
  endif ()
  if (APIMU_LD_EXTEND_STACK)
    set_target_properties     (${TARGET} PROPERTIES LINK_FLAGS "-Wl,-z,stack-size=10000000")
  endif ()
  if (APIMU_MACOS_LD_EXTEND_STACK)
    set_target_properties     (${TARGET} PROPERTIES LINK_FLAGS "-Wl,-stack_size,10000000")
  endif ()
  if (APIMU_LINK_EXTEND_STACK)
    set_target_properties     (${TARGET} PROPERTIES LINK_FLAGS "/STACK:10000000")
  endif ()
  if (IPO_SUPPORTED)
    set_target_properties     (${TARGET} PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
  endif ()
endmacro ()

# Add targets
add_executable (testcore
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/procs.cpp
  src/elab/tableau.cpp
  src/testcore.cpp)
target_default_compile_options  (testcore)
target_include_directories      (testcore PRIVATE src)

add_executable (testeval
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/procs.cpp
  src/elab/elab.cpp
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/eval/tree.cpp
  src/eval/evaluator.cpp
  src/eval/exteval.cpp
  src/testeval.cpp)
target_default_compile_options  (testeval)
target_include_directories      (testeval PRIVATE src)

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

if (FALSE)

# See: https://stackoverflow.com/questions/49768454/whats-the-differences-between-pthread-and-pthread-options-in-cmake
set (THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads)

add_executable (testserver
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/server/jsonrpc2.cpp
  src/server/languageserver.cpp
  src/server/lsp.cpp
  src/testserver.cpp)
target_default_compile_options  (testserver)
target_include_directories      (testserver PRIVATE src)
target_link_libraries           (testserver PRIVATE nlohmann_json::nlohmann_json Threads::Threads)
#target_precompile_headers       (testserver PRIVATE ${nlohmann_json_SOURCE_DIR}/single_include/nlohmann/json.hpp)

endif ()

enable_testing ()
add_executable (testtest
  test/testtest.cpp)
target_default_compile_options  (testtest)
target_include_directories      (testtest PRIVATE src)

add_test (testtest testtest)
