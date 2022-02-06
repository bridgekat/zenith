cmake_minimum_required(VERSION 3.20)

project(ApiMu VERSION 0.1 LANGUAGES CXX)

include(CheckIPOSupported)
check_ipo_supported(RESULT ipo_supported)

add_executable              (parser src/lexer.cpp src/parser.cpp)
target_compile_features     (parser PRIVATE cxx_std_20)
set_target_properties       (parser PROPERTIES CXX_EXTENSIONS OFF)
if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-Wall>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-Wextra>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-Wdeprecated>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-Weffc++>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_CONCEPT_CHECKS>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG>")
  target_compile_options    (parser PRIVATE "$<$<CONFIG:Debug>:-D_GLIBCXX_DEBUG_PEDANTIC>")
endif ()
