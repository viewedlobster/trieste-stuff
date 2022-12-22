#pragma once

#include "lang.hh"

namespace list
{
  using namespace wf::ops;

  inline constexpr auto wf_literal = Integer | String;

  inline constexpr auto wf_parse_token = wf_literal | List;

  // A <<= B indicates that B is a child of A
  // ++ indicates that there are zero or more instances of the token
  inline constexpr auto wf_parser =
      (Top <<= File)
    | (File <<= Group)
    | (List <<= (ListContents | Group))
    | (ListContents <<= Group++)
    | (Group <<= wf_parse_token++)
    ;
}