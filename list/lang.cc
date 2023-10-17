#include "lang.hh"
#include "wf.hh"

namespace list
{
  PassDef cleanup()
  {
    return {
      "cleanup",
      wf_pass_cleanup,
      dir::topdown,
      {
        In(Top) * (T(File) << T(Group)[Group]) >>
        [](Match& _) { return Group << *_[Group]; },
  
        In(File) * (T(List) << T(ListContents)[ListContents]) >>
        [](Match& _) { return List << *_[ListContents]; },
  
        In(Group) * (T(List) << T(ListContents)[ListContents]) >>
        [](Match& _) { return List << *_[ListContents]; }
  
      }
    };
  }

  Driver& driver()
  {
    static Driver d(
      "list",
      nullptr,
      parser(),
      {
        cleanup()
      }
    );
    return d;
  }
}