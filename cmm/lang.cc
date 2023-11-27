#include "lang.hh"
#include "wf.hh"
#include <iostream>

using namespace std;

namespace cmm
{

auto err(const NodeRange& r, const std::string& msg)
{
    return Error << (ErrorMsg ^ msg) << (ErrorAst << r);
}

auto err(Node node, const std::string& msg)
{
    return Error << (ErrorMsg ^ msg) << (ErrorAst << node);
}

std::string getNodeName(Node node)
  {
    std::string text(node->location().view());
    return text;
  }


PassDef parse_funs() 
  {
    return {
      "funs",
      wf_parse_funs,
      dir::topdown,
      { //file contains a program  
        In(Top) * T(File)[File] >>
          [](Match& _) {
            return Program << *_[File]; 
          },
        // a program consists of function definitions at top level
        In(Program) * T(Group) << 
        (T(Ident)[Type] * T(Ident)[Ident] * (T(Paren)[Paren] 
          //<< ~(T(Comma,Group,Assign)[Parameter])) 
          << ((T(Comma)[Parameter]) / ~(T(Group)[Parameter] / T(Assign)[Parameter]))) 
          * T(Block)[Block]) >>
          [](Match& _) {
            return FunDef << _[Type] << _[Ident] << (ParamList << _[Parameter]) << _[Block]; },
      
        // retrieve parameters if several
        T(ParamList) << T(Comma)[Comma] >> // e.g. f(int x, int y){} function def
          [](Match& _) {
            return ParamList << *_[Comma]; 
          },
        // 
        In (ParamList) * T(Group)[Group] << (T(Ident) * T(Ident) * End) >>
          [](Match& _) {
            return Parameter << *_[Group];
          },
        In (ParamList) * T(Assign)[Assign] >>
          [](Match& _) {
            return Parameter << _[Assign];
          },

        // Error rules 
        // Only fundefs at top level allowed
        In(Program) * T(Group)[Group] >>
          [](Match& _) {
            return Error << (ErrorMsg ^ "Can only have function definitions on top level") << (ErrorAst << _[Group]);
          },
        // Parameters should be declared with a type and an id
        In(ParamList) * T(Group)[Group] >>
          [](Match& _) {
            return err(_[Group], "Expecting parameters to have a type and an id");
          }
      }
    };
  }

PassDef parse_statements()
  {
    return {
      "statements",
      wf_parse_statements,
      dir::topdown,
      {
        T(Group)[Group] << (T(If) * (T(Paren) << T(Group)[Expr]) * T(Block)[Block])  >>
          [](Match& _) {
         return Statement << (If << (Expr << *_[Expr]) << _[Block]);
          },
        // lift else statements 
        T(Group)[Group] << (T(Else) * T(Block)[Block])  >>
          [](Match& _) {
            return Statement << (Else << _[Block]);
          },
         // lift elseif statements 
        T(Group)[Group] << (T(ElseIf) * T(Block)[Block])  >>
          [](Match& _) {
            return Statement << (ElseIf << _[Block]);
          },
        // all if's/elseif's will be nested under the first if.
        In(Block) * ((T(Statement) << T(If)[If]) * (T(Statement) << T(If,Else,ElseIf)[ElseIf])) >>
           [](Match& _) {
             return Statement << ((IfElse << _[If]) << (ElseIf << _[ElseIf])); 
           },
        // // // continue nesting of elseifs 
        In(Block) * (T(Statement) << T(IfElse)[If]) * (T(Statement) << T(If,Else,ElseIf)[ElseIf]) >>
           [](Match& _) {
           return Statement << ((IfElse << *_[If]) << (ElseIf << _[ElseIf])); 
          },
        In(IfElse) * T(If)[If] * T(If)[IfElse]>>
          [](Match& _) {
            return If << *_[If] << IfElse << _[IfElse]; 
          },
        // // continue nesting of elseifs 
        // T(ElseIf)[ElseIf] * T(If,ElseIf,Else)[Else] >>
        //   [](Match& _) {
        //     return ElseIf << *_[ElseIf] << _[Else]; 
        // },
        // Assignments with declarations
        In(Assign) * ((T(Group) << (T(Ident)[Type] 
          * T(Ident)[Id] * End)) * T(Group)[Expr]) >>
          [](Match& _) {
            return Seq << (Decl << _[Type] << _[Id]) << _[Expr];
          },
        // Reassignments 
        T(Assign) << ((T(Group) << T(Ident)[Ident] * End) * T(Group)[Expr]) >>
          [](Match& _) {
            return ReAssign << (_[Ident]) << _[Expr];
          },

        // Return statements 
        In(Block) * (T(Group)[Group] << (T(Return) * Any++[Rhs])) >>
          [](Match& _) {
            return Statement << (Return << (Expr << _[Rhs]));
          },
        // other statements (any ; terminated group)
        // In(Block) * T(Group)[Statement] * End >> 
        //   [](Match& _) {
        //     return Statement << *_[Statement];
        // },


        // Expressions 

        // function call expressions
        // e.g. f(10); function call 

        // changed to two separate rules to wrap them as exprs more easily
        // T(Ident)[Ident] * (T(Paren) 
        //   << (T(Comma)[Parameter] / ~T(Group)[Parameter])) * End >> 
        //   [](Match& _) {
        //     return Expr << (FunCall << _[Ident] << (ArgList << _[Parameter])); 
        //   },

        // fun call 
        In(Expr,Group) * (T(Ident)[Ident] * T(Paren)[Paren] * End) >> // e.g. f();
          [](Match& _) {
            return FunCall << _[Ident] << (ArgList << *_[Paren]); 
        },
        // function call as a statement
        In(Block) * T(Group) << T(FunCall)[FunCall] >>
          [](Match& _) {
            return Statement << _(FunCall);
        },

        // lift comma-separated arguments one level 
        In(FunCall) * (T(Ident)[Ident] * (T(ArgList) << T(Comma)[Comma])) >>
          [](Match& _) {
              return Seq << _[Ident] << (ArgList << *_[Comma]);           
          }, 

        //wrap all arguments as exprs 
        In(ArgList) * T(Group)[Expr] >> 
          [](Match& _) {
            return Expr << *_[Expr];
        },

        // rhs of assignments are expressions 
        In(Assign,ReAssign) * (T(Decl,Ident)[Lhs] * T(Group)[Rhs]) >>
          [](Match& _) {
            return Seq << _(Lhs) <<(Expr << *_[Rhs]);
        },


        // Error rules 
        // statements can only appear in blocks
        // this one makes everything stuck. 
        // In(Block)[Block] * --T(Statement) >>
        //    [](Match& _) {
        //     return err(_[Block], "Block contains something that is not a statement");
        //    },
        //  else without if
        In(Block) * (Start * T(Else)[Else]) >>
          [](Match& _) {
            return err(_[Else], "Cannot have an else statement without an if"); 
       }
      }
    };
  }

  // PassDef exprs(){

  // }

  PassDef cleanup()
  {
    return {
      "cleanup",
      wf_parser,
      dir::topdown,
      {
        In(Top) * (T(File) << T(Group)[Group]) >>
        [](Match& _) { return Group << *_[Group]; }
      }
    };
  }

  Driver& driver()
  {
    static Driver d(
      "cmm",
      nullptr,
      parser(),
      {
        parse_funs()
       ,parse_statements()
        //,cleanup()
      }
    );
    return d;
  }
}

