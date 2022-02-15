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
    # - unmatchedSuppression needed since not all source files are
    #   analyzed simultaneously
    # - unusedFunction needed since not all source files are
    #   analyzed simultaneously
    # - template needed to force "warning" into output string, and
    #   to make the 'id' available for suppression
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
  if (ipo_supported)
    set_target_properties   (${TARGET} PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
  endif ()
endmacro ()

# Add targets
add_executable (testcore
  src/core/context.cpp
  src/core/expr.cpp
  src/core/proof.cpp
  src/testcore.cpp)
target_default_compile_options  (testcore)
target_include_directories      (testcore PRIVATE src include)

add_executable (testparsing
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/testparsing.cpp)
target_default_compile_options  (testparsing)
target_include_directories      (testparsing PRIVATE src include)

add_executable (testserver
  src/testserver.cpp)
target_default_compile_options  (testserver)
target_include_directories      (testserver PRIVATE src deps/json-rpc-cxx/include deps/json-rpc-cxx/vendor)
if (WIN32)
  target_link_libraries         (testserver wsock32 ws2_32)
endif ()

add_executable (testclient
  src/testclient.cpp)
target_default_compile_options  (testclient)
target_include_directories      (testclient PRIVATE src deps/json-rpc-cxx/include deps/json-rpc-cxx/vendor)
if (WIN32)
  target_link_libraries         (testclient wsock32 ws2_32)
endif ()
