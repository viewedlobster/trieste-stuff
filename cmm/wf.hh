#pragma once

#include "lang.hh"

namespace cmm
{
  using namespace wf::ops;

  inline const auto wf_primtypes = Ident 
                                 | Int 
                                 | Double
                                 | Bool 
                                 | Void; 

  inline const auto wf_stms = IfElse
                            | ElseIf 
                            | If 
                            | Else
                            | While 
                            | Return
                            | Block
                            | Assign
                            | Term;

  inline const auto wf_parse_token = Paren
                                   | Group 
                                   | ParamList
                                   ;
                                   

  inline const auto wf_operators = Mul | Div | Add | Sub 
                                 | Inc | Dec 
                                 | LE  | GE | LT | GT | EQ | NEQ  
                                 | And | Or;  
                                                        

  // A <<= B indicates that B is a child of A
  // ++ indicates that there are zero or more instances of the token

  inline const auto wf_parser =
    (Top <<= File)
  | (File <<= Group++)
  | (Paren <<= (Assign | Comma | Group)++) // allows default params
  | (Block <<= (Assign | Group)++) 
  | (Assign <<= Group++)
  | (Comma <<= Group++[2])
  | (Group <<= (wf_parse_token | wf_primtypes | wf_stms | wf_operators)++[1])
  ;


  inline const auto wf_parse_funs =
      (Top <<= Program)
    | (Program <<= FunDef++)
    | (FunDef <<= Ident * Ident * ParamList * Block)
    | (ParamList <<= (Parameter | Assign)++) // a function has 0 or more parameters
    | (Parameter <<= Ident * Ident) // a parameter is a type and an id, only in fun defs
    | (Paren <<= (Comma | Group)++) // we want 0 or 1
    | (Comma <<= Group++) 
    | (Block <<= (Assign | Group)++)
    | (Assign <<= (Group * Group))
    | (Group <<= (wf_parse_token | wf_primtypes | wf_stms | wf_operators)++[1])
    ;


  inline const auto wf_parse_statements =
     (Top <<= Program)
    | (Program <<= FunDef++)
    | (FunDef <<= Ident * Ident * ParamList * Block)
    | (ParamList <<= Parameter++) // a function has 0 or more parameters
    | (Parameter <<= (Decl | Assign)++) // a parameter is a type and an id
    | (Expr <<= (wf_operators | wf_primtypes | FunCall | Group)++)
    | (FunCall <<= Ident * ArgList)
    | (ArgList <<= Expr++)
    | (Block <<= (Assign | Statement)++)
    | (Assign <<= (Lhs >>= Decl) * (Rhs >>= Expr))
    | (ReAssign <<= (Lhs >>= Ident) * (Rhs >>= Expr))
    | (Decl <<= (Type >>= Ident) * Ident) 
    | (Statement <<= (Expr | FunCall | Assign | Return | If | IfElse | ElseIf | Else))
    | (Return <<= Expr)
    | (If <<= Expr * Block) 
    | (IfElse <<= If * ElseIf)
    | (ElseIf <<= (IfElse | Else)++)
    | (Else <<= Block)
    ;

  // instead of Expr nodes 
  //inline const auto exprs = (wf_operators | wf_primtypes | FunCall)++;

}