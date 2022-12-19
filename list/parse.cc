#include <trieste/driver>

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

			"[" >> [](auto& m) { m.push(Bracket) }, // left bracket

			"]" >> [](auto& m) { m.pop(Bracket) },
			}
	}
}
