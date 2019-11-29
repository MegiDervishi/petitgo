%{
  open Go_ast
%}

/* token */
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

/* Priority */
/* %nonassoc IF ELSE */



%nonassoc LT GT LEQ GEQ
%nonassoc DOT
%nonassoc sign pointer ADDRESS NOT 

%left OR AND 
%left ISEQ NEQ
%left PLUS MINUS MULT DIV MOD


%start program
%type <Go_ast.fichier> program

%%
sep_list_plus(sep, X):
    | x = X; sep? { [x] }
    | x = X; sep; xs = sep_list_plus(sep, X) { x::xs }

sep_list_star(sep, X):
    | sep? { [] }
    | x = X; sep; xs = sep_list_star(sep, X) { x::xs }

program :
  | PACKAGE; id = IDENT; SEMICOL; IMPORT; s = STRING; SEMICOL; d = decl* ; EOF
    { if id = "main" && s = "fmt" then d else raise Error }
  | PACKAGE; id = IDENT; SEMICOL; d = decl*; EOF
    { if id = "main" then d else raise Error}

decl : 
  | TYPE; id = IDENT; STRUCT; LBRACE; v = sep_list_plus(SEMICOL, vars) ; RBRACE; SEMICOL
    { Tdecl (id, v) }
  | TYPE; id = IDENT; STRUCT; LBRACE; RBRACE; SEMICOL
    { Tdecl (id, []) }
  | FUNC; id = IDENT; LPAREN; v = sep_list_star(COMMA, vars); RPAREN; tr = type_retour?; b = bloc; SEMICOL
    { TFunc (id, v, tr, b )} (*autorise none as a tr *)
  | FUNC; id = IDENT; LPAREN; RPAREN; tr = type_retour?; b = bloc
    { TFunc (id, [] , tr, b )}

vars :
  | l_id = sep_list_plus(COMMA, IDENT); t = type_go { (l_id , t)}

type_retour :
  | t = type_go 
    { Tretour t } (*%prec sign*)
  | LPAREN; l_t = sep_list_plus(COMMA,type_go); RPAREN 
    { Tretour_list t l_t }

type_go :
  | id = IDENT          { Tident id }
  | MULT; tg = type_go  { Tmult tg }

expression :
  | c = constant        
    { Econst c }
  | LPAREN; e = expression; RPAREN { e }
  | id = IDENT 
    { Evar id }
  | e = expression; DOT; i = IDENT 
    { Edot (e, i) }
  | id = IDENT; LPAREN; le = seperated_list(COMMA, expression); RPAREN 
    { Esthsth (id, le) } (*check*)
  | f = IDENT; DOT; p = IDENT; LPAREN; le = seperated_list(COMMA, expression); RPAREN
    { if f="fmt" && p="Print" then Eprint le else raise Error }
  | NOT; e = expression     { Eunop (NOT, e)    }
  | MINUS; e = expression   { Eunop (MINUS, e)  }
  | ADDRESS; e = expression { Eunop (ADDRESS, e)}
  | MULT; e = expression    { Eunop (MULT, e)   }
  | e1 = expression; ISEQ ; e2 = expression { Ebinop (Iseq , e1, e2) }
  | e1 = expression; ISEQ ; e2 = expression { Ebinop (Iseq , e1, e2) }
  | e1 = expression; ISEQ ; e2 = expression { Ebinop (Iseq , e1, e2) }
  
constant :
  | i = INT     { Tint i }
  | s = STRING  { Tstring s }
  | t = TRUE    { Tbool t }
  | f = FALSE   { Tbool f }
  | n = NIL     { Tnil n }





