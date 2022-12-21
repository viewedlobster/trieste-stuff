#ifndef __LANG_HH
#define __LANG_HH
#include <trieste/driver.h>

namespace list
{
  using namespace trieste;

  inline constexpr auto List = TokenDef("list");
  inline constexpr auto ListContents = TokenDef("contents");

  inline constexpr auto Integer = TokenDef("int", flag::print);
  inline constexpr auto String = TokenDef("string", flag::print);

  Parse parser();
  Driver& driver();
}

#endif
