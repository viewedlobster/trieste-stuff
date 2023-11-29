#include "lang.h"
#include "wf.h"

namespace shrubbery
{

  auto err(const NodeRange& r, const std::string& msg)
  {
    return Error << (ErrorMsg ^ msg) << (ErrorAst << r);
  }

  auto err(Node node, const std::string& msg)
  {
    return Error << (ErrorMsg ^ msg) << (ErrorAst << node);
  }

  // TODO: Blocks containing only alts should not be blocks
  PassDef clean_parsing()
  {
    return {
      "clean parsing",
      wf_clean_parser,
      dir::topdown,
      {
        // An empty block followed by alternatives is ignored
        (T(Block) << (T(Group) << (T(Alt)[Alt]))) >>
          [](Match& _) { return _(Alt); },

        // A semicolon that causes an empty group is ignored
        (In(Semi) * ((T(Group)[Group] << End))) >>
          [](Match& _) { return Seq << *_[Group]; },

        // Opener-closer pairs must have comma-separated groups
        (In(Paren, Brace, Bracket) * Any * Any)[Group] >>
          [](Match& _) { return err(_[Group], "Groups in parentheses/braces/brackets must be comma separated"); },

        // Opener-closer pairs may contain empty blocks
        (--(In(Paren, Brace, Bracket, Comma, File))) * ((T(Group) << ((!T(Block))++ * (T(Block)[Block] << End)))) >>
          [](Match& _) { return err(_[Block], "Blocks may not be empty"); },

        // Top-level groups may consist of *only* an empty block
        In(File) * (T(Group) << (((!T(Block)) * (!T(Block))++ * (T(Block)[Block] << End)))) >>
          [](Match& _) { return err(_[Block], "Blocks may not be empty"); },

        // Alternatives cannot be empty
        T(Alt)[Alt] << End >>
          [](Match& _) { return err(_[Alt], "Alternatives may not be empty"); },
      }};
  }

  PassDef drop_separators()
  {
    return {
      "drop separators",
      wf_drop_separators,
      dir::topdown,
      {
        (T(Comma)[Comma]) >>
          [](Match& _) { return Seq << *_[Comma]; },

        T(Semi)[Semi] >>
          [](Match& _) { return Seq << *_[Semi]; },
      }
    };
  }


  Driver& driver()
  {
    static Driver d(
      "shrubbery",
      nullptr,
      parser(),
      {
          clean_parsing(),
          drop_separators(),
      });

    return d;
  }
}
