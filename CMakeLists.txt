cmake_minimum_required (VERSION 3.15)

project (
  ApiMu
  VERSION       0.1.0
  DESCRIPTION   ""
  HOMEPAGE_URL  ""
  LANGUAGES     CXX
)

list (PREPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/extern/prelude/cmake")
include (Prelude NO_POLICY_SCOPE)

# ===== Dependencies =====
# See: https://stackoverflow.com/questions/49768454/whats-the-differences-between-pthread-and-pthread-options-in-cmake
set (THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads REQUIRED)

# See: https://json.nlohmann.me/integration/cmake/#fetchcontent
set (JSON_Install OFF CACHE INTERNAL "")
set (JSON_MultipleHeaders ON)
FetchContent_Declare (nlohmann_json URL https://github.com/nlohmann/json/releases/download/v3.11.2/json.tar.xz)
FetchContent_MakeAvailable (nlohmann_json)

# ===== Targets =====
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
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/eval/tree.cpp
  src/eval/evaluator.cpp
  src/eval/extended_evaluator.cpp
  src/testeval.cpp)
target_default_compile_options  (testeval)
target_include_directories      (testeval PRIVATE src)

add_executable (testserver
  src/core/context.cpp
  src/core/expr.cpp
  src/core/fol/fol.cpp
  src/elab/procs.cpp
  src/parsing/lexer.cpp
  src/parsing/parser.cpp
  src/eval/tree.cpp
  src/eval/evaluator.cpp
  src/eval/extended_evaluator.cpp
  src/server/json_rpc_server.cpp
  src/server/document.cpp
  src/server/lsp.cpp
  src/testserver.cpp)
target_default_compile_options  (testserver)
target_include_directories      (testserver PRIVATE src)
target_link_libraries           (testserver PRIVATE Threads::Threads nlohmann_json::nlohmann_json)

# ===== Tests =====
enable_testing ()

add_executable (testtest
  tests/testtest.cpp)
target_default_compile_options  (testtest)
target_include_directories      (testtest PRIVATE src)
add_test                        (testtest testtest)
