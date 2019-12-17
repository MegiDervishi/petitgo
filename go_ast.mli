
type pos = Lexing.position
type tuple = pos * pos
type 'a loc = 'a * tuple

type ident = string
type  unop = Not | Sign | Address | Pointer

type binop = Iseq| Neq  | Lt| Leq | Gt | Geq|
             Add | Minus| Mult | Div| Mod| 
             And | Or   

type constant =
  | Eint64 of int64 
  | Estring of string 
  | Ebool of bool
  | ENil

(* Types for the parser *)
type expr = 
  | Econst of constant 
  | Eident of ident 
  | Emethod of expr loc * ident
  | Eprint of expr loc list 
  | Ecall of ident * expr loc list 
  | Eunop of unop * expr loc 
  | Ebinop of binop * expr loc * expr loc 

type type_go =
  | Tident of ident 
  | Tmult of type_go loc
  | Nonetype_go

type type_retour = 
  | Tretour of type_go loc 
  | Tretour_list of type_go loc list  
  | Nonetype_ret

type instr_simple =
  | Isexpr of expr loc 
  | Isassign_incdec of expr loc * expr loc 
  | Isassign_list of expr loc list * expr loc list
  | Isref of ident list * expr loc list 

type instr =
  | Inil 
  | Iinstrsimpl of instr_simple loc 
  | Iblock of block loc 
  | Iif of instr_if loc 
  | Ivar of ident list * type_go loc * expr loc list 
  | Ireturn of expr loc list
  | Ifor of expr loc * block loc 

and block = instr loc list
and instr_if = expr loc * block loc * block loc 

type vars = ident list * type_go loc 
type gofunc = ident * vars loc list * type_retour loc * block loc 
type structure = ident * vars loc list 


type decl = 
  | Dstruct of structure loc
  | Dfunc of gofunc loc

type program = decl list 

type typ = 
    | Tint
    | Tbool
    | Tstring
    | Tstruct of string
    | Tstar of typ
    | Tnone
    | Tvoid

type gotype = 
    | Tsimpl of typ 
    | Tmany of typ list