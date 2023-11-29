#pragma once

#include "lang.h"

namespace shrubbery
{
  using namespace wf::ops;

  inline const auto wf_parse_tokens = Paren | Bracket | Brace |
      Block | Alt | Atom;

  // clang-format off

  inline const auto wf_parser =
      (Top <<= File)
    | (File <<= (Group | Semi)++)
    | (Paren <<= (Group | Comma)++)
    | (Bracket <<= (Group | Comma)++)
    | (Comma <<= Group++[2])
    | (Semi <<= Group++[1])
    | (Block <<= (Group | Semi)++) // TODO: When can blocks be empty?
    | (Alt <<= (Group | Semi)++)
    | (Group <<= wf_parse_tokens++)
    ;

  inline const auto wf_clean_parser =
      (Top <<= File)
    | (File <<= (Group | Semi)++)
    | (Paren <<= (Group | Comma)++)
    | (Bracket <<= (Group | Comma)++)
    | (Comma <<= Group++[2])
    | (Semi <<= Group++[1])
    | (Block <<= (Group | Semi)++) // TODO: When can blocks be empty?
    | (Alt <<= (Group | Semi)++[1])
    | (Group <<= wf_parse_tokens++)
    ;

  inline const auto wf_drop_separators =
      (Top <<= File)
    | (File <<= Group++)
    | (Paren <<= Group++)
    | (Bracket <<= Group++)
    | (Block <<= Group++)
    | (Alt <<= Group++[1])
    | (Group <<= wf_parse_tokens++);
  // clang-format on
}
