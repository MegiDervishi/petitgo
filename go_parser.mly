%{
  open Go_ast
  exception ParsingError

  let checknone typenone  = function
    | None -> typenone
    | Some t -> t
  

%}

/* Declare tokens */
%token IF ELSE FOR FUNC
%token IMPORT PACKAGE
%token VAR STRUCT TYPE
%token TRUE FALSE NIL RETURN
%token MULT DIV MOD ADD MINUS
%token INCR DECR
%token AND OR
%token EQUAL ISEQ NEQ REF
%token LEQ GEQ LT GT 
%token NOT ADDRESS 
%token DOT
%token LPAREN RPAREN LBRACE RBRACE 
%token SEMICOL COMMA
%token EOF
	    
%token <string> STRING
%token <string> IDENT 

/* Priority and associativity*/
/* %nonassoc IF ELSE */
%nonassoc DOT 
%nonassoc LT GT LEQ GEQ
%left OR AND 
%left ISEQ NEQ
%left ADD MINUS MULT DIV MOD
%nonassoc sign  pointer ADDRESS NOT 

%start program
%type <Go_ast.program> program

/* Grammar rules */
%%

sep_list_plus(sep, X):
    | x = X; sep? { [x] }
    | x = X; sep; xs = sep_list_plus(sep, X) { x::xs };

sep_list_star(sep, X):
    | x = X; sep? { [] }
    | x = X; sep; xs = sep_list_star(sep, X) { x::xs };

program :
  | PACKAGE; id = IDENT; SEMICOL; IMPORT; s = STRING; SEMICOL; d = decl* ; EOF
    { if id = "main" && s = "fmt" then d else raise ParsingError }
  | PACKAGE; id = IDENT; SEMICOL; d = decl*; EOF
    { if id = "main" then d else raise ParsingError};

decl : 
  | s = structure { Dstruct s }
  | f = gofunc    { Dfunc f }

structure:
  | TYPE; id = IDENT; STRUCT; LBRACE; v = sep_list_plus(SEMICOL, vars) ; RBRACE; SEMICOL
    { (id, v) }
  | TYPE; id = IDENT; STRUCT; LBRACE; RBRACE; SEMICOL
    { (id, []) }

gofunc :
  | FUNC; id = IDENT; LPAREN; v = sep_list_plus(COMMA, vars); RPAREN; tr = type_retour?; b = block; SEMICOL
    { (id, v, checknone Nonetype_ret tr, b )} (* main (a b,)*)
  | FUNC; id = IDENT; LPAREN; RPAREN; tr = type_retour?; b = block; SEMICOL
    { (id, [] , checknone Nonetype_ret tr, b )} (* main () *)
  

vars :
  | l_id = separated_nonempty_list(COMMA, IDENT); t = type_go { (l_id , t)};

type_retour :
  | t = type_go { Tretour t }
  | LPAREN; l_t = sep_list_plus(COMMA,type_go); RPAREN 
    { Tretour_list l_t };

type_go :
  | id = IDENT          { Tident id }
  | MULT; tg = type_go  { Tmult tg };

constant :
  | s = STRING  { Cstring s }
  | t = TRUE    { Cbool true  }
  | f = FALSE   { Cbool false }
  | n = NIL     { Nil };

expr :
  | c = constant                { Econst c }
  | LPAREN; e = expr; RPAREN    { e }
  | id = IDENT                  { Evar id }
  | e = expr; DOT; i = IDENT    { Emethod (e, i) }
  | id = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN 
    { Ecall (id, le) }
  | f = expr; DOT; p = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN
    { if f= Evar "fmt" && p="Print" then Eprint le else raise ParsingError }
  | NOT; e = expr               { Eunop (Not, e)    }
  | MINUS; e = expr             { Eunop (Sign, e)  } %prec sign
  | ADDRESS; e = expr           { Eunop (Address, e)}
  | MULT; e = expr              { Eunop (Pointer, e)   } %prec pointer
  | e1 = expr; ISEQ ; e2 = expr { Ebinop (Iseq , e1, e2) }
  | e1 = expr; NEQ  ; e2 = expr { Ebinop (Neq , e1, e2) }
  | e1 = expr; LT   ; e2 = expr { Ebinop (Lt , e1, e2) }  
  | e1 = expr; LEQ  ; e2 = expr { Ebinop (Leq , e1, e2) }
  | e1 = expr; GT   ; e2 = expr { Ebinop (Gt , e1, e2) }
  | e1 = expr; GEQ  ; e2 = expr { Ebinop (Geq , e1, e2) }
  | e1 = expr; ADD  ; e2 = expr { Ebinop (Add , e1, e2) }
  | e1 = expr; MINUS; e2 = expr { Ebinop (Minus , e1, e2) }
  | e1 = expr; MULT ; e2 = expr { Ebinop (Mult , e1, e2) }
  | e1 = expr; DIV  ; e2 = expr { Ebinop (Div , e1, e2) }
  | e1 = expr; MOD  ; e2 = expr { Ebinop (Mod , e1, e2) }
  | e1 = expr; AND  ; e2 = expr { Ebinop (And , e1, e2) }
  | e1 = expr; OR   ; e2 = expr { Ebinop (Or , e1, e2) };

block :
  | LBRACE; bl = sep_list_plus(SEMICOL, instr); RBRACE { bl }
  | LBRACE; RBRACE { [] };

instr_simple :
  | e = expr       { Isexpr e }
  | e = expr; INCR { Isid (Incr, e) }
  | e = expr; DECR { Isid (Decr, e) }
  | le1 = separated_nonempty_list(COMMA, expr); EQUAL;  le2 = separated_nonempty_list(COMMA, expr)
    { Isequal (le1, le2) }
  | lid = separated_nonempty_list(COMMA, IDENT); REF; le = separated_nonempty_list(COMMA, expr)
    { Isref (lid, le)}; (* problem once a pointer u always have to use := to use = change it to var*)

instr :
  | SEMICOL          { Inil}
  | s = instr_simple { I_s  s }
  | b  = block       { I_b  b }
  | f = instr_if     { I_if f }
  | VAR; v = separated_nonempty_list(COMMA, IDENT); t = type_go? 
    { Ivar (v, checknone Nonetype_go t, [])}
  | VAR; v = separated_nonempty_list(COMMA, IDENT); t = type_go?; EQUAL; le =separated_nonempty_list(COMMA, expr)
    { Ivar (v , checknone Nonetype_go t, le) }
  | RETURN; le = separated_list(COMMA, expr) 
    { Ireturn le }
  | FOR; b = block 
    { Ifor (Econst (Cbool true), b) }
  | FOR; e = expr; b = block 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = expr; SEMICOL; b = block 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = expr; SEMICOL; i2 = instr_simple; b = block 
    { Ifor (e, b @ [I_s i2]) }
  | FOR; i1 = instr_simple; SEMICOL; e = expr; SEMICOL;  b = block 
    { I_b [I_s i1; Ifor (e, b)] }
  | FOR; i1 = instr_simple; SEMICOL; e = expr; SEMICOL; i2 = instr_simple; b = block 
    { I_b [I_s i1; Ifor (e, b @ [I_s i2])] }
  | RETURN; l = separated_list(COMMA, expr) {Ireturn l}

instr_if :
  | IF; e = expr; b = block { (e, b, [])}
  | IF; e = expr; b1 = block; ELSE; b2 = block { (e, b1, b2)}
  | IF; e = expr; b1 = block; ELSE; b2 = instr_if { (e, b1, [ I_if b2]) };


