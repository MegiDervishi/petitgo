
type  unop = Not | Sign | Address | Pointer

type binop = Iseq| Neq  | Lt| Leq | Gt | Geq|
             Add | Minus| Mult | Div| Mod| 
             And | Or   

type expr = 
  | Eint64 of int64 
  | Estring of string 
  | Ebool of bool
  | ENil
  | Eident of string
  | Emethod of expr * string
  | Ecall of string * expr list 
  | Eprint of expr list 
  | Eunop of unop * expr 
  | Ebinop of binop * expr * expr

type type_go =
  | Tident of string 
  | Tmult of type_go
  | Nonetype_go

type type_retour = 
  | Tretour of type_go
  | Tretour_list of type_go list 
  | Nonetype_ret

type instr_simple =
  | Isexpr of expr
  | Isassign of expr * expr
  | Isassign_list of expr list * expr list
  | Isref of string list * expr list 

type instr =
  | Inil 
  | Iinstrsimpl of instr_simple
  | Iblock of block
  | Iif of instr_if
  | Ivar of string list * type_go * expr list 
  | Ireturn of expr list
  | Ifor of expr * block

and block = instr list 
and instr_if = expr * block * block

type vars = string list * type_go
type gofunc = string * vars list * type_retour * block
type structure = string * vars list 


type decl = 
  | Dstruct of structure
  | Dfunc of gofunc

type program = decl list 