cmake_minimum_required(VERSION 3.14.0)
project(trieste-stuff VERSION 0.1.0 LANGUAGES CXX)

include(FetchContent)

FetchContent_Declare(
  trieste
  GIT_REPOSITORY https://github.com/microsoft/Trieste
  GIT_TAG 31a6bf3d6beabf3e14dda688eff6ba76016f8878        
  )

FetchContent_MakeAvailable(trieste)

add_executable(cmm
  lang.cc
  parse.cc
  main.cc
  )

target_link_libraries(cmm
  CLI11::CLI11
  trieste::trieste
  )


set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED True)
