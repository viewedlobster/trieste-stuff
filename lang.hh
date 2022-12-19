#ifndef __LANG_HH
#define __LANG_HH

namespace list
{
	using namespace trieste;

	inline constexpr auto Bracket = TokenDef("bracket");

	inline constexpr auto Integer = TokenDef("int", flag::print);
	inline constexpr auto String = TokenDef("string", flag::print);
}

#endif
