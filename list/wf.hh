#pragma once

#include "lang.hh"

namespace list
{
  using namespace wf::ops;

  inline const auto wf_literal = Integer | String;

  inline const auto wf_parse_token = wf_literal | List;

  // A <<= B indicates that B is a child of A
  // ++ indicates that there are zero or more instances of the token
  inline const auto wf_parser =
      (Top <<= File)
    | (File <<= Group)
    | (List <<= (ListContents | Group))
    | (ListContents <<= Group++)
    | (Group <<= wf_parse_token++)
    ;

  inline const auto wf_pass_cleanup =
      (Top <<= Group)
    | (List <<= Group++)
    | (Group <<= wf_parse_token++)
    ;
}