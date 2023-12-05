#include "lang.h"
#include "wf.h"

namespace shrubbery
{

  // There are some Rhombus specific things that are not supported:
  // - Line- and Column-insensitivity with << and >>
  // - Continuing a line with backslash
  // - Group comments with #// //#
  // - At-notation
  // - Keywords prefixed by ~
  //
  // Things that I plan to implement
  // - Indented continuation of operators
  // - Single quotes
  //
  // Other TODOs:
  // - Better parsing of strings
  Parse parser()
  {
    Parse p(depth::file, wf_parser);
    auto indent = std::make_shared<std::vector<Location>>();
    auto fresh = std::make_shared<bool>(true);
    auto newline = std::make_shared<bool>(false);

    auto push_indentation = [fresh, indent](auto& m) {
        if (!*fresh) return;

        *fresh = false;
        auto loc = m.match();
        if (!indent->empty()) {
            auto last_loc = indent->back();
            auto last_col = last_loc.linecol().second;
            auto col = loc.linecol().second;
            if (col <= last_col) {
                m.error("New indentation level must be larger than the previous");
            }
        }
        indent->push_back(loc);
    };

    auto pop_indentation = [indent, fresh]() {
        // If we have not set an indentation, don't pop
        if (*fresh) {
            *fresh = false;
            return;
        }
        indent->pop_back();
    };

    auto match_indentation = [pop_indentation, newline, fresh, indent](auto& m) {
        if (!*newline) {
            return true;
        }
        *newline = false;

        auto loc = m.match();
        auto last_loc = indent->back();
        auto [line, col] = loc.linecol();
        auto [last_line, last_col] = last_loc.linecol();

        while (last_line < line && col < last_col) {
            pop_indentation();
            if (indent->empty()) {
                m.error("Indentation is before left-most group");
                indent->push_back(last_loc);
                return false;
            }

            m.term();
            if (m.in(Block)) {
                m.pop(Block);
                m.term();
            } else if (m.in(Alt)) {
                m.pop(Alt);
                m.term();
            }

            last_loc = indent->back();
            last_line = last_loc.linecol().first;
            last_col = last_loc.linecol().second;
        }

        if (line != last_line && col != last_col) {
            m.error("Group does not match any previous indentation");
            return false;
        }

        return true;
    };

    auto open_pair = [match_indentation, push_indentation, fresh](auto& m) {
        push_indentation(m);

        if (match_indentation(m)) {
            *fresh = true;
            return true;
        }
        return false;
    };

    auto close_all = [pop_indentation, fresh, indent](auto& m, std::initializer_list<Token> tokens) {
      *fresh = false;

      bool progress = true;
      while (progress) {
        progress = false;
        for (auto& token : tokens) {
          if (m.in(token) || m.group_in(token)) {
            m.term({token});
            progress = true;
            if (!indent->empty() && (token == Block || token == Alt)) {
                pop_indentation();
            }
            break;
          }
        }
      }
    };

    auto close_pair = [close_all, match_indentation, pop_indentation, newline, indent](auto &m) {
        pop_indentation();

        match_indentation(m);
        close_all(m, {Block, Alt, Semi});
        m.term({Comma});
    };

    auto add_atom = [match_indentation, push_indentation, fresh, newline](auto &m) {
        if (*newline)
            m.term();

        push_indentation(m);

        if (match_indentation(m))
            m.add(Atom);
    };

    p("start",
      {
        // Whitespace between tokens.
        "[[:blank:]]+" >> [](auto&) { }, // no-op

        "[\r\n]+" >>  [newline](auto&) {
            *newline = true;
        }, // no-op

        // String literals
        // TODO: Should probably be more clever... Modes?
        R"("[^"]*")" >>
          [add_atom](auto& m) { add_atom(m); },

        // Everything that is not a special character is an Atom

        // Identifiers
        R"([[:alpha:]_][[:alnum:]_]*)" >>
          [add_atom](auto& m) { add_atom(m); },

        // Integers
        // TODO: Floating-point numbers, etc.
        "[[:digit:]]+" >>
          [add_atom](auto& m) { add_atom(m); },

        // Operators
        // TODO: Handle indentation
        R"([!#$%&<>\^?|=+\-*/.:]*[!#$%&<>\^?=*]|[!#$%&<>\^?|=+\-*/.:]+[!#$%&<>\^?|=*]|\.+|\++|-+|::+)" >>
          [add_atom](auto& m) {
              // TODO: Handle indentation
              add_atom(m);
          },

        // Opener-closer pairs
        R"((\())" >>
          [open_pair](auto& m) { if (open_pair(m)) m.push(Paren, 1); },

        R"((\[))" >>
          [open_pair](auto& m) { if (open_pair(m)) m.push(Bracket, 1); },

        R"((\{))" >>
          [open_pair](auto& m) { if (open_pair(m)) m.push(Brace, 1); },

        R"(\))" >>
          [close_pair, fresh, indent](auto& m) {
              close_pair(m);
              m.pop(Paren);
          },

        R"(\])" >>
          [close_pair, fresh, indent](auto& m) {
              close_pair(m);
              m.pop(Bracket);
          },

        R"(\})" >>
          [close_pair, fresh, indent](auto& m) {
              close_pair(m);
              m.pop(Brace);
          },

        // Commas separate groups in opener-closer pairs
        "," >>
          [close_all, fresh, newline](auto& m) {
              if (*newline) {
                  m.error("A comma cannot start a line");
                  *newline = false;
              }

              // Handle empty blocks
              if (*fresh && m.in(Block))
                  m.pop(Block);

              close_all(m, {Block, Alt, Semi});

              m.seq(Comma);
          },

        // Semicolons separate groups outside of opener-closer pairs
        ";" >>
          [newline, fresh](auto& m) {
              if (*newline) {
                  m.error("A semicolon cannot start a line");
                  return;
              }

              m.seq(Semi);
          },

        // Blocks
        ":" >>
          [match_indentation, fresh](auto& m) {
              match_indentation(m);
              m.push(Block);
              *fresh = true;
          },

        // Alternatives
        R"(\|)" >>
        [match_indentation, fresh](auto& m) {
            if (match_indentation(m)) {
                if (m.group_in(Alt)) {
                    m.seq(Alt);
                } else {
                    m.push(Alt);
                    *fresh = true;
                }
            }
        }
    });

    p.done([close_all, indent](auto& m) {
        close_all(m, {Block, Alt, Semi});
        while (!indent->empty()) {
            indent->pop_back();
        }
    });

    return p;
  }
}
