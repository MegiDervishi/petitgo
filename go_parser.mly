%{
  open Go_ast

  let checknone typenone  = function
    | None -> typenone
    | Some t -> t
  let checknone_loc typenone locs = 
    let (ty, pos) = locs in (checknone typenone ty, pos)

  let rec makeexpr_to_ident = function
    | (Eident i) :: x -> i :: (makeexpr_to_ident x)
    | [] -> []
    | _ -> raise Error

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
%token <int64>  INT


/* Priority and associativity*/
%nonassoc DOT 
%nonassoc LT GT LEQ GEQ
%left OR AND 
%left ISEQ NEQ
%left ADD MINUS MULT DIV MOD
%nonassoc sign pointer ADDRESS NOT 

%start program
%type <Go_ast.program> program

/* Grammar rules */
%%

%inline loc(X):
  | x = X {x, ($startpos, $endpos)}
;

sep_list_plus(sep, X):
    | x = X; sep? { [x] }
    | x = X; sep; xs = sep_list_plus(sep, X) { x::xs };

program :
  | PACKAGE; id = IDENT; SEMICOL; IMPORT; s = STRING; SEMICOL; d = decl* ; EOF
    { if id = "main" && s = "fmt" then d else raise Error }
  | PACKAGE; id = IDENT; SEMICOL; d = decl*; EOF
    { if id = "main" then d else raise Error};

decl : 
  | s = loc(structure) { Dstruct s }
  | f = loc(gofunc)    { Dfunc f }

structure:
  | TYPE; id = IDENT; STRUCT; LBRACE; v = sep_list_plus(SEMICOL, loc(vars)) ; RBRACE; SEMICOL
    { (id, v) }
  | TYPE; id = IDENT; STRUCT; LBRACE; RBRACE; SEMICOL
    { (id, []) }

gofunc :
  | FUNC; id = IDENT; LPAREN; v = sep_list_plus(COMMA, loc(vars)); RPAREN; tr = loc(type_retour?); b = loc(block); SEMICOL
    { (id, v, checknone_loc Nonetype_ret tr, b )} (* main (a b,)*)
  | FUNC; id = IDENT; LPAREN; RPAREN; tr = loc(type_retour?); b = loc(block); SEMICOL
    { (id, [] , checknone_loc Nonetype_ret tr, b )} (* main () *)
  
vars :
  | l_id = separated_nonempty_list(COMMA, IDENT); t = loc(type_go) { (l_id , t)};

type_retour :
  | t = loc(type_go) { Tretour t }
  | LPAREN; l_t = sep_list_plus(COMMA, loc(type_go)); RPAREN 
    { Tretour_list l_t };

type_go :
  | id = IDENT               { Tident id }
  | MULT; tg = loc(type_go)  { Tmult tg };

constant :
  | i = INT     { Eint64 i }
  | s = STRING  { Estring s }
  | TRUE        { Ebool true  }
  | FALSE       { Ebool false }
  | NIL         { ENil }

expr :
  | c = constant { Econst c }
  | id = IDENT  { Eident id }
  | LPAREN; e = expr; RPAREN    { e }
  | e = loc(expr); DOT; i = IDENT    { Emethod (e, i) }
  | id = IDENT; LPAREN; le = separated_list(COMMA, loc(expr)); RPAREN 
    { Ecall (id, le) }
  | f = expr; DOT; p = IDENT; LPAREN; le = separated_list(COMMA, loc(expr)); RPAREN 
    { if f = Eident "fmt" && p="Print" then Eprint le else raise Error }
  | MINUS; e = loc(expr)   %prec sign          
    { Ebinop (Minus, (Econst (Eint64 Int64.zero) , ($startpos,$endpos)), e)  } 
  | MULT; e = loc(expr)              { Eunop (Pointer, e)   } %prec pointer
  | op = unop1 ; e = loc(expr)       { Eunop (op, e)}
  | e1 = loc(expr); op = binop; e2 = loc(expr) { Ebinop (op, e1, e2)};

block :
  | LBRACE; bl = sep_list_plus(SEMICOL, loc(instr)); RBRACE { bl }
  | LBRACE; RBRACE { [] };

instr_simple :
  | e = loc(expr) { Isexpr e }
  | e = loc(expr); INCR 
    { Isassign (e, (Ebinop(Add, e, (Econst (Eint64 Int64.one), ($startpos,$endpos))),($startpos,$endpos)))} 
  | e = loc(expr); DECR
    { Isassign (e, (Ebinop(Minus, e, (Econst (Eint64 Int64.one), ($startpos,$endpos))),($startpos,$endpos)))} 
  | le1 = separated_nonempty_list(COMMA, loc(expr)); EQUAL; le2 = separated_nonempty_list(COMMA, loc(expr))
    { Isassign_list (le1, le2) }
  | lid = separated_nonempty_list(COMMA, expr); REF; le = separated_nonempty_list(COMMA, loc(expr))
    { Isref (makeexpr_to_ident lid, le)};

instr_if :
  | IF; e = loc(expr); b = loc(block) { (e, b, ([],($startpos, $endpos)))}
  | IF; e = loc(expr); b1 = loc(block); ELSE; b2 = loc(block) { (e, b1, b2)}
  | IF; e = loc(expr); b = loc(block); ELSE; i = loc(instr_if) 
    { let _,pos = i in (e, b, ([(Iif i,pos)],pos))};

instr :
  | SEMICOL               { Inil }
  | s = loc(instr_simple) { Iinstrsimpl s }
  | b = loc(block)        { Iblock  b }
  | f = loc(instr_if)     { Iif f }
  | VAR; v = separated_nonempty_list(COMMA, IDENT); t = loc(type_go?) 
    { Ivar (v, checknone_loc Nonetype_go t, [])}
  | VAR; v = separated_nonempty_list(COMMA, IDENT); t = loc(type_go?); EQUAL; le =separated_nonempty_list(COMMA, loc(expr))
    { Ivar (v , checknone_loc Nonetype_go t, le) }
  | RETURN; le = separated_list(COMMA, loc(expr)) 
    { Ireturn le }
  | FOR; b = loc(block) 
    { let _,pos = b in Ifor((Econst (Ebool true),pos), b)}
  | FOR; e = loc(expr); b = loc(block) 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = loc(expr); SEMICOL; b = loc(block) 
    { Ifor (e, b) }
  | FOR; SEMICOL; e = loc(expr); SEMICOL; i2 = loc(instr_simple); b = loc(block) 
    { let tb, pos1 = b in let _, pos2 = i2 in 
      Ifor (e, (tb @ [(Iinstrsimpl i2, pos2)], pos1)) }
  | FOR; i = loc(instr_simple); SEMICOL; e = loc(expr); SEMICOL; b = loc(block) 
    { let _,pos1 = i in 
      Iblock ([(Iinstrsimpl i, pos1); (Ifor (e, b),($startpos,$endpos))],($startpos,$endpos))}
  | FOR; i1 = loc(instr_simple); SEMICOL; e = loc(expr); SEMICOL; i2 = loc(instr_simple); b = loc(block) 
    { let _,pos1 = i1 in let _,pos2 = i2 in let tb, pos3 = b in 
    Iblock ([(Iinstrsimpl i1, pos1); (Ifor (e, (tb@[(Iinstrsimpl i2, pos2)],pos1)),($startpos,$endpos))], ($startpos,$endpos))}


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
