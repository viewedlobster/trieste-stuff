#ifndef __LANG_HH
#define __LANG_HH
#include <trieste/driver.h>

namespace list
{
  using namespace trieste;

  inline const auto List = TokenDef("list");
  inline const auto ListContents = TokenDef("contents");

  inline const auto Integer = TokenDef("int", flag::print);
  inline const auto String = TokenDef("string", flag::print);

  Parse parser();
  Driver& driver();
}

#endif
