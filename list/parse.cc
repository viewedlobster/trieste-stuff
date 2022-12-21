#include <trieste/driver.h>

#include "lang.hh"

/*
 * [1, 2, 3]
 * [     4, 3    , 3 ]
 */

namespace list
{
  Parse parser()
  {
    Parse p(depth::file);
    auto indent = std::make_shared<std::vector<size_t>>();

    p("start",
      {
        // whitespace
        "[[:blank:]]+" >> [](auto&) {}, // no-op

        // integers
        "-?[[:digit:]]+" >> [](auto& m) { m.add(Integer); },

        // commas
        "," >> [](auto& m) { m.seq(ListContents); },

        // brackets
        R"(\[)" >> [](auto& m) { m.push(List, 1); }, // left bracket

        R"(\])" >> [](auto& m) { m.term({ListContents}); m.pop(List); }, // right bracket
      });
    return p;
  }
}
