#include <trieste/driver.h>

#include "wf.hh"
#include "lang.hh"

/*
 * [1, 2, 3]
 * [     4, 3    , 3 ]
 */

namespace cmm
{
  const std::initializer_list<Token> terminators = {Comma, Assign};

  
  Parse parser()
  {
    Parse p(depth::file, wf_parser);
    auto indent = std::make_shared<std::vector<size_t>>();

    p("start",
      {
        // whitespace
        "[[:space:]]+" >> [](auto&) {}, // no-op

        // Assign.
        "=" >> [](auto& m) { m.seq(Assign); },

        // statement term.
        ";" >> [](auto& m) { 
            m.term({Assign});},

        // Keywords.
        "return" >> [](auto& m) { m.add(Return); },
        "elseif" >> [](auto& m) { m.add(ElseIf); },
        "else" >> [](auto& m) { m.add(Else); },
        "if" >> [](auto& m) { m.add(If); },
        "while" >> [](auto& m) { m.add(While); },

        // Identifier.
        R"([_[:alpha:]][_[:alnum:]]*\b)" >> [](auto& m) { m.add(Ident); },

          // Curly braces.
        R"((\{)[[:blank:]]*)" >>
          [indent](auto& m) {
            // we push a Block node. Subsequent nodes will be added
            // as its children.
          m.push(Block, 1);
            
          },

        R"(\})" >>
          [indent](auto& m) {
           
            // pop back up out of the block
            m.pop(Block);
             // terminate the current group
            m.term({});
          },

        "," >> [](auto& m) { 
          m.seq(Comma, {Assign});
          },

          // paren.
        R"((\()[[:blank:]]*)" >>
          [indent](auto& m) {
            // we push a paren node. Subsequent nodes will be added
            // as its children.
            m.push(Paren, 1);
          },

        R"(\))" >>
          [indent](auto& m) {
            // terminate the current group
            m.term({Assign, Comma});
            // pop back up out of the Paren
            m.pop(Paren);
          },

        // Float.
        R"([[:digit:]]+\.[[:digit:]]+(?:e[+-]?[[:digit:]]+)?\b)" >>
          [](auto& m) { m.add(Double); },

        // integers
        "-?[[:digit:]]+" >> [](auto& m) { m.add(Int); },

         // Line comment.
        "//[^\n]*" >> [](auto&) {}, // no-op
        
        // Block comment /* .... */
        //"//*[^]**/" >> [](auto&) {}, // no-op

        // Pre-processor directives
        "#[^\n]*" >> [](auto&) {}, // no-op
        
        // built-in operations
        R"(\+\+)" >> [](auto& m) { m.add(Inc); },
        "--" >> [](auto& m) { m.add(Dec); },

        // Add ('+' is a reserved RegEx character)
        R"(\+)" >> [](auto& m) { m.add(Add); },
        // Subtract
        "-" >> [](auto& m) { m.add(Sub); },
        // Multiply ('*' is a reserved RegEx character)
        R"(\*)" >> [](auto& m) { m.add(Mul); },
        // Divide
        "/" >> [](auto& m) { m.add(Div); },

        // Comparison
        "<=" >> [](auto& m) { m.add(LE); },
        "<" >> [](auto& m) { m.add(LT); },
        ">=" >> [](auto& m) { m.add(GE); },
        ">" >> [](auto& m) { m.add(GT); },
        "==" >> [](auto& m) { m.add(EQ); },
        "!=" >> [](auto& m) { m.add(NEQ); },

        // Boolean comparison
        "&&" >> [](auto& m) { m.add(And); },
        "||" >> [](auto& m) { m.add(Or); }

        // commas
        //"," >> [](auto& m) { m.seq(ListContents); },

        // brackets
        //R"(\[)" >> [](auto& m) { m.push(List, 1); }, // left bracket

        //R"(\])" >> [](auto& m) { m.term({ListContents}); m.pop(List); }, // right bracket



      });
    return p;
  }
}
