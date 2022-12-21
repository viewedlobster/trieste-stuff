#include "lang.hh"
#include "wf.hh"

namespace list
{
  Driver& driver()
  {
    static Driver d(
      "list",
      parser(),
      wf_parser(),
      {});

    return d;
  }
}