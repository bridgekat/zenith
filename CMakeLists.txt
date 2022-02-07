cmake_minimum_required (VERSION 3.20)

project (ApiMu VERSION 0.1 LANGUAGES CXX)

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

