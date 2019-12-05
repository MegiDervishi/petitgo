%{
  open Go_ast
  exception ParsingError

  let checknone typenone  = function
    | None -> typenone
    | Some t -> t
  
  let rec makeexpr_to_ident = function
    | (Eident i) :: x -> i :: (makeexpr_to_ident x)
    | [] -> []
    | _ -> raise ParsingError
%}

/* Declare tokens */
%token VAR STRUCT TYPE TRUE FALSE NIL RETURN
%token EQUAL ISEQ NEQ REF LEQ GEQ LT GT 
%token IF ELSE FOR FUNC IMPORT PACKAGE
%token INCR DECR AND OR NOT ADDRESS 
%token LPAREN RPAREN LBRACE RBRACE 
%token MULT DIV MOD ADD MINUS
%token DOT SEMICOL COMMA
%token EOF
	    
%token <string> STRING
%token <string> IDENT
%token <int64> INT


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

program :
  | PACKAGE; id = IDENT; SEMICOL; IMPORT; s = STRING; SEMICOL; d = decl* ; EOF
    { if id = "main" && s = "fmt" then d else raise ParsingError }
  | PACKAGE; id = IDENT; SEMICOL; d = decl*; EOF
    { if id = "main" then d else raise ParsingError};

decl : 
  | s = structure { s }
  | f = gofunc    { f }

structure:
  | TYPE; id = IDENT; STRUCT; LBRACE; v = sep_list_plus(SEMICOL, vars) ; RBRACE; SEMICOL
    { Dstruct(id, v) }
  | TYPE; id = IDENT; STRUCT; LBRACE; RBRACE; SEMICOL
    { Dstruct(id, []) }

gofunc :
  | FUNC; id = IDENT; LPAREN; v = sep_list_plus(COMMA, vars); RPAREN; tr = type_retour?; b = block; SEMICOL
    { Dfunc(id, v, checknone Nonetype_ret tr, b )} (* main (a b,)*)
  | FUNC; id = IDENT; LPAREN; RPAREN; tr = type_retour?; b = block; SEMICOL
    { Dfunc(id, [] , checknone Nonetype_ret tr, b )} (* main () *)
  
vars :
  | l_id = separated_nonempty_list(COMMA, IDENT); t = type_go { (l_id , t)};

type_retour :
  | t = type_go { Tretour t }
  | LPAREN; l_t = sep_list_plus(COMMA,type_go); RPAREN 
    { Tretour_list l_t };

type_go :
  | id = IDENT          { Tident id }
  | MULT; tg = type_go  { Tmult tg };

expr :
  | i = INT     { Eint64 i }
  | s = STRING  { Estring s }
  | t = TRUE    { Ebool true  }
  | f = FALSE   { Ebool false }
  | n = NIL     { ENil }
  | LPAREN; e = expr; RPAREN    { e }
  | id = IDENT                  { Eident id }
  | e = expr; DOT; i = IDENT    { Emethod (e, i) }
  | id = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN 
    { Ecall (id, le) }
  | f = expr; DOT; p = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN
    { if f= Eident "fmt" && p="Print" then Eprint le else raise ParsingError }
  | MINUS; e = expr             { Eunop (Sign, e)  } %prec sign
  | MULT; e = expr              { Eunop (Pointer, e)   } %prec pointer
  | op = unop1 ; e = expr       { Eunop (op, e)}
  | e1 = expr; op = binop; e2 = expr { Ebinop (op, e1, e2)}

block :
  | LBRACE; bl = sep_list_plus(SEMICOL, instr); RBRACE { bl }
  | LBRACE; RBRACE { [] };

instr_simple :
  | e = expr       { Isexpr e }
  | e = expr; INCR { Isid  (Incr, e) } /*check this for int64*/
  | e = expr; DECR { Isid (Decr, e) }
  | le1 = separated_nonempty_list(COMMA, expr); EQUAL;  le2 = separated_nonempty_list(COMMA, expr)
    { Isassign (le1, le2) }
  | lid = separated_nonempty_list(COMMA, expr); REF; le = separated_nonempty_list(COMMA, expr)
    { Isref (makeexpr_to_ident lid, le)};

instr :
  | SEMICOL          { Inil }
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
    { Ifor ( Ebool true, b) }
  | FOR; e = expr; b = block 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = expr; SEMICOL; b = block 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = expr; SEMICOL; i2 = instr_simple; b = block 
    { Ifor (e, b @ [I_s i2]) }
  | FOR; i1 = instr_simple; SEMICOL; e = expr; SEMICOL; b = block 
    { I_b [I_s i1; Ifor (e, b)] }
  | FOR; i1 = instr_simple; SEMICOL; e = expr; SEMICOL; i2 = instr_simple; b = block 
    { I_b [I_s i1; Ifor (e, b @ [I_s i2])] }

instr_if :
  | IF; e = expr; b = block { (e, b, [])}
  | IF; e = expr; b1 = block; ELSE; b2 = block { (e, b1, b2)}
  | IF; e = expr; b1 = block; ELSE; b2 = instr_if { (e, b1, [ I_if b2]) }

  %inline binop:
    ISEQ  {Iseq}
  | NEQ   {Neq}
  | LT    {Lt}  
  | LEQ   {Leq} 
  | GT    {Gt} 
  | GEQ   {Geq}
  | ADD   {Add} 
  | MINUS {Minus}
  | MULT  {Mult}
  | DIV   {Div}
  | MOD   {Mod}
  | AND   {And}
  | OR    {Or}

  %inline unop1:
  | ADDRESS {Address}
  | NOT { Not }
  ;
