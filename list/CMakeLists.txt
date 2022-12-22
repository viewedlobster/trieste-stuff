cmake_minimum_required(VERSION 3.14.0)
project(trieste-stuff VERSION 0.1.0 LANGUAGES CXX)

include(FetchContent)

FetchContent_Declare(
  trieste
  GIT_REPOSITORY https://github.com/microsoft/Trieste
  GIT_TAG        bbdfdf1554941b9cadfb8b0977c5114284b43363
  )

FetchContent_MakeAvailable(trieste)

add_executable(list
  lang.cc
  parse.cc
  main.cc
  )

target_link_libraries(list
  CLI11::CLI11
  trieste::trieste
  )


set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)
