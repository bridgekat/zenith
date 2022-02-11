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


add_executable (testcore
  src/core/context.cpp
  src/core/expr.cpp
  src/core/proof.cpp
  src/testcore.cpp)
target_compile_features     (testcore PRIVATE cxx_std_20)
set_target_properties       (testcore PROPERTIES CXX_EXTENSIONS OFF)
target_include_directories  (testcore PRIVATE src)
if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-Wall>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-Wextra>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-Wdeprecated>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-Weffc++>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_CONCEPT_CHECKS>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG>")
  target_compile_options    (testcore PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG_PEDANTIC>")
endif ()
if (ipo_supported)
  message (STATUS "IPO / LTO enabled")
  set_target_properties     (testcore PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()


add_executable (testparsing
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/testparsing.cpp)
target_compile_features     (testparsing PRIVATE cxx_std_20)
set_target_properties       (testparsing PROPERTIES CXX_EXTENSIONS OFF)
target_include_directories  (testparsing PRIVATE src)
if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-Wall>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-Wextra>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-Wdeprecated>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-Weffc++>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_CONCEPT_CHECKS>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG>")
  target_compile_options    (testparsing PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG_PEDANTIC>")
endif ()
if (ipo_supported)
  message (STATUS "IPO / LTO enabled")
  set_target_properties     (testparsing PROPERTIES INTERPROCEDURAL_OPTIMIZATION TRUE)
endif()

