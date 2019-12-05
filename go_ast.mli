type type_go =
  | Tident of string 
  | Tmult of type_go
  | Nonetype_go

type type_retour = 
  | Tretour of type_go
  | Tretour_list of type_go list 
  | Nonetype_ret

type constant = 
  | Cstring of string 
  | Cbool of bool
  | Nil

type  unop = Not | Sign | Address | Pointer

type binop = Iseq| Neq  | Lt| Leq | Gt | Geq|
             Add | Minus| Mult | Div| Mod| 
             And | Or   

type expr = 
  | Econst of constant
  | Evar of string
  | Emethod of expr * string
  | Ecall of string * expr list 
  | Eprint of expr list 
  | Eunop of unop * expr 
  | Ebinop of binop * expr * expr

type incrdecr = Incr | Decr 

type instr_simple =
  | Isexpr of expr
  | Isid of incrdecr * expr
  | Isequal of expr list * expr list
  | Isref of string list * expr list 
  (*| Nonetype_is*)

type instr =
  | Inil 
  | I_s of instr_simple
  | I_b of block
  | I_if of instr_if
  | Ivar of string list * type_go * expr list 
  | Ireturn of expr list
  | Ifor of expr * block
  (*| Ifor_ieb of instr_simple * expr * instr_simple * block  *)
and block = instr list 
and instr_if = expr * block * block

type vars = string list * type_go
type gofunc = string * vars list * type_retour * block
type structure = string * vars list 


type decl = 
  | Dstruct of structure
  | Dfunc of gofunc

type program = decl list 
