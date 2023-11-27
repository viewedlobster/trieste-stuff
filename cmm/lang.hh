#pragma once

#include <trieste/driver.h>

namespace cmm
{
  using namespace trieste;

  // Program
  inline const auto Program = TokenDef("program");
  inline const auto Block = TokenDef("block");
  inline const auto Paren = TokenDef("paren");
  inline const auto Comma = TokenDef(",");
 

  // Definitions 
  inline const auto FunDef  = TokenDef("fundef", flag::symtab | flag::defbeforeuse);
  inline const auto FunCall = TokenDef("funcall");



  inline const auto DefUse  = TokenDef("funuse");
  inline const auto DefType = TokenDef("deftype");

  inline const auto ParamList = TokenDef("paramlist");
  inline const auto Parameter = TokenDef("param");

  //Arguments
  inline const auto Arg = TokenDef("arg");
  inline const auto ArgList = TokenDef("arguments");
  

  // types 
  inline const auto Int = TokenDef("int", flag::print);
  inline const auto Double = TokenDef("float", flag::print);
  inline const auto Bool = TokenDef("bool", flag::print);
  inline const auto Char = TokenDef("char");
  inline const auto Void = TokenDef("void");
  

  // Statements -- any expression followed by ;
  inline const auto Statement = TokenDef("statement");
  inline const auto If        = TokenDef("if"); // an if with two children (a condition expr and a then stmt) 
  inline const auto Else      = TokenDef("else");
  inline const auto ElseIf    = TokenDef("elseif");
  inline const auto IfElse    = TokenDef("ifelse");
  inline const auto While     = TokenDef("while");
  inline const auto Return    = TokenDef("return");
  inline const auto Decl      = TokenDef("decl");


  // Good to have
  inline const auto Term = TokenDef(";");
  inline const auto Equals = TokenDef("equals");
  inline const auto Ident = TokenDef("ident", flag::print);

  inline const auto Print = TokenDef("print");
  inline const auto String = TokenDef("string", flag::print);

  inline const auto Calculation =
    TokenDef("calculation", flag::symtab | flag::defbeforeuse);
  inline const auto Expr = TokenDef("expr");
  inline const auto Assign = TokenDef("assign", flag::lookup);
  inline const auto ReAssign = TokenDef("reassign", flag::lookup | flag::shadowing);
  inline const auto Output = TokenDef("output");
  inline const auto Ref = TokenDef("ref");

  // built-in operations 
  inline const auto Add = TokenDef("+");
  inline const auto Sub = TokenDef("-");
  inline const auto Mul = TokenDef("*");
  inline const auto Div = TokenDef("/");
  
  // Boolean operations 
  inline const auto And = TokenDef("&&");
  inline const auto Or = TokenDef("||");

  // Operations on numbers 
  inline const auto LT = TokenDef("<");
  inline const auto LE = TokenDef("<=");
  inline const auto GT = TokenDef(">");
  inline const auto GE = TokenDef(">=");
  inline const auto EQ = TokenDef("==");
  inline const auto NEQ = TokenDef("!=");

  inline const auto Inc = TokenDef("++");
  inline const auto Dec = TokenDef("--");


  inline const auto Literal = TokenDef("literal");

  // convenient id tokens
  inline const auto Id = TokenDef("id");
  inline const auto Type = TokenDef("type");
  inline const auto Op = TokenDef("op");
  inline const auto Lhs = TokenDef("lhs");
  inline const auto Rhs = TokenDef("rhs");

  Parse parser();
  Driver& driver();
}