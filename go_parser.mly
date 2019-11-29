%{
  open Go_ast
  exception ParsingError
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
%token LE GE LT GT 
%token NOT ADDRESS DOT
%token LPAREN RPAREN LBRACE RBRACE SEMICOL COMMA
%token EOF
	    
%token <int> INT
%token <string> STRING
%token <string> IDENT 

/* Priority and associativity*/
/* %nonassoc IF ELSE */
%nonassoc LT GT LEQ GEQ
%nonassoc DOT
%nonassoc sign pointer ADDRESS NOT 

%left OR AND 
%left ISEQ NEQ
%left PLUS MINUS MULT DIV MOD

%start program
%type <Go_ast.fichier> program

/* Grammar rules */
%%
sep_list_plus(sep, X):
    | x = X; sep? { [x] }
    | x = X; sep; xs = sep_list_plus(sep, X) { x::xs };

sep_list_star(sep, X):
    | sep? { [] }
    | x = X; sep; xs = sep_list_star(sep, X) { x::xs };

program :
  | PACKAGE; id = IDENT; SEMICOL; IMPORT; s = STRING; SEMICOL; d = decl* ; EOF
    { if id = "main" && s = "fmt" then d else raise Error }
  | PACKAGE; id = IDENT; SEMICOL; d = decl*; EOF
    { if id = "main" then d else raise Error};

decl : 
  | TYPE; id = IDENT; STRUCT; LBRACE; v = sep_list_plus(SEMICOL, vars) ; RBRACE; SEMICOL
    { Dstruct (id, v) }
  | TYPE; id = IDENT; STRUCT; LBRACE; RBRACE; SEMICOL
    { Dstruct (id, []) }
  | FUNC; id = IDENT; LPAREN; v = sep_list_star(COMMA, vars); RPAREN; tr = type_retour?; b = block; SEMICOL
    { Dfunc (id, v, tr, b )} (*autorise None as a tr *)
  | FUNC; id = IDENT; LPAREN; RPAREN; tr = type_retour?; b = block
    { Dfunc (id, [] , tr, b )};

vars :
  | l_id = sep_list_plus(COMMA, IDENT); t = type_go { (l_id , t)};

type_retour :
  | t = type_go { Tretour t }
  | LPAREN; l_t = sep_list_plus(COMMA,type_go); RPAREN 
    { Tretour_list t l_t };

type_go :
  | id = IDENT          { Tident id }
  | MULT; tg = type_go  { Tmult tg };

constant :
  | i = INT     { Cint i }
  | s = STRING  { Cstring s }
  | t = TRUE    { Cbool true  }
  | f = FALSE   { Cbool false }
  | n = NIL     { Nil };

expr :
  | c = constant                { Econst c }
  | LPAREN; e = expr; RPAREN    { e }
  | id = IDENT                  { Evar id }
  | e = expr; DOT; i = IDENT    { Edot (e, i) }
  | id = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN 
    { Esthsth (id, le) } (*check*)
  | f = IDENT; DOT; p = IDENT; LPAREN; le = separated_list(COMMA, expr); RPAREN
    { if f="fmt" && p="Print" then Eprint le else raise Error }
  | NOT; e = expr               { Eunop (Not, e)    }
  | MINUS; e = expr             { Eunop (Minus, e)  } %prec sign
  | ADDRESS; e = expr           { Eunop (Address, e)}
  | MULT; e = expr              { Eunop (Mult, e)   } %prec pointer
  | e1 = expr; ISEQ ; e2 = expr { Ebinop (Iseq , e1, e2) }
  | e1 = expr; NEQ  ; e2 = expr { Ebinop (Noteq , e1, e2) }
  | e1 = expr; LT   ; e2 = expr { Ebinop (Lt , e1, e2) }  
  | e1 = expr; LEQ  ; e2 = expr { Ebinop (Leq , e1, e2) }
  | e1 = expr; GT   ; e2 = expr { Ebinop (Gt , e1, e2) }
  | e1 = expr; LEQ  ; e2 = expr { Ebinop (Leq , e1, e2) }
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
  | e = expr { ISexpr e }
  | e = expr INCR { ISinc e }
  | e = expr DECR { ISdec e }
  | le1 = separated_nonempty_list(COMMA, expr) EQUAL  le2 = separated_nonempty_list(COMMA, expr)
    { ISequal le1 le2 }
  | lid = separated_nonempty_list(COMMA, IDENT) REF le = separated_nonempty_list(COMMA, expr);

instr_if :
  | IF; e = expr; b = block { (e, b, [])}
  | IF; e = expr; b1 = block; ELSE; b2 = block { (e, b1, b2)}
  | IF; e = expr; b1 = block; ELSE; b2 = instr_if { (e, b1, [ Inif b2]) };

instr :
  | s = instr_simple { I_s  s }
  | b  = block        { I_b  b }
  | f = instr_if     { I_if f }
  | VAR; v = separated_nonempty_list(COMMA, ident); t = type_go? 
    { Ivar (v, t, [])}
  | VAR; v = separated_nonempty_list(COMMA, ident); t = type_go?; EQUAL; le =separated_nonempty_list(COMMA, expr)
    { Ivar (v , t, le) }
  | RETURN; le = separated_list(COMMA, expr) 
    { Ireturn le }
  | FOR; b = block 
    { Ifor (Econst (Cbool true), b)}
  | FOR; e = expr; b = block 
    { Ifor (e, b)}
  | FOR; is1 = instr_simple?; SEMICOL; e = expr; SEMICOL; is2 = instr_simple?; b = block 
    { Ifor_ieb (is1, e, is2, b)}




