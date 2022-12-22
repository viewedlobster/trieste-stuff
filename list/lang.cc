#include "lang.hh"
#include "wf.hh"

namespace list
{
  PassDef cleanup()
  {
    return {
      In(Top) * (T(File) << T(Group)[Group]) >>
      [](Match& _) { return Group << *_[Group]; },

      In(File) * (T(List) << T(ListContents)[ListContents]) >>
      [](Match& _) { return List << *_[ListContents]; },

      In(Group) * (T(List) << T(ListContents)[ListContents]) >>
      [](Match& _) { return List << *_[ListContents]; }

    };
  }

  Driver& driver()
  {
    static Driver d(
      "list",
      parser(),
      wf_parser(),
      {{"cleanup", cleanup(), wf_pass_cleanup()}});

    return d;
  }
}