cmake_minimum_required(VERSION 3.14.0)
project(trieste-shrubbery VERSION 0.1.0 LANGUAGES CXX)

include(FetchContent)

FetchContent_Declare(
  trieste
  GIT_REPOSITORY "https://github.com/EliasC/Trieste"
  GIT_TAG features/group_in
  )

FetchContent_MakeAvailable(trieste)

add_executable(shrubbery
  src/lang.cc
  src/parse.cc
  src/main.cc
  )

target_link_libraries(shrubbery
  CLI11::CLI11
  trieste::trieste
  )

install(DIRECTORY examples DESTINATION shrubbery)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)
