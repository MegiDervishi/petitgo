{
  open Lexing
  open Go_parser

  let keywords = Hashtbl.create 99
  let () = List.iter (fun (s,t) -> Hashtbl.add keywords s t)
      ["else", ELSE; "for", FOR; "func", FUNC; "if", IF; 
      "import", IMPORT;  "package", PACKAGE; "struct", STRUCT;
      "type", TYPE; "var", VAR;]
  let keys_colon = Hashtbl.create 3
  let () = List.iter (fun (s,t) -> Hashtbl.add keys_colon s t)
      ["true", TRUE;"false", FALSE;"nil", NIL; "return", RETURN;]

  let alpha = ['a'-'z' 'A'-'Z' '_']
  let number = ['0'-'9']
  let ident = alpha (alpha | number)*

  let hexa = ['0'-'9' 'a'-'f' 'A'-'F']
  let entier = number+ | (('0x' '0X') hexa+)

  (*possible error '\'*)
  let car = [' '| '!'| '#'-'['| ']'-'~'| "\\\\"| "\\\""| "\\n"| "\\t"]
  let chaine = "\"" car* "\""

  let space = [' ' '\t']
  let semicolon = ref false;
}

rule token = parse
  | "\n"        { new_line lexbuf; 
                if !semicolon then semicolon:= false; SEMICOL
                else token lexbuf }
  | space+      { token lexbuf }
  | "main"      { semicolon := true; IDENT "main" }
  | "Print"     { semicolon := true; IDENT "Print"}
  | "\"fmt\""   { semicolon := true; STRING "fmt" }
  | "fmt"       { semicolon := true; IDENT "fmt"  }
  | "/*"        { comment1 lexbuf }
  | "//"        { comment2 lexbuf }
  | entier as e { semicolon := true; INT(int_of_string e) }
  | chaine as c { semicolon := true; STRING c }
  | "&&"        { semicolon := false; AND }
	| "||"        { semicolon := false; OR }
	| "=="        { semicolon := false; ISEQ }
  | "!="        { semicolon := false; NEQ }
  | ">"         { semicolon := false; GT }
  | ">="        { semicolon := false; GEQ }
  | "<"         { semicolon := false; LT }
	| "<="        { semicolon := false; LE }
	| ":="        { semicolon := false; REF }
  | "="         { semicolon := false; EQUAL}
	| "++"        { semicolon := true;  INCR }
	| "--"        { semicolon := true;  DECR }
	| "+"         { semicolon := false; ADD }
	| "-"         { semicolon := false; MINUS }
	| "*"         { semicolon := false; MULT }
	| "/"         { semicolon := false; DIV }
	| "%"         { semicolon := false; MOD }
	| "&"         { semicolon := false; ADDRESS }
	| "!"         { semicolon := false; NOT }
  | "."         { semicolon := false; DOT }
	| "("         { semicolon := false; LPAREN }
  | ")"         { semicolon := true;  RPAREN }
  | "{"         { semicolon := false; LBRACE }
  | "}"         { semicolon := true;  RBRACE }
	| ";"         { semicolon := false; SEMICOL}
	| ","         { semicolon := false; COMMA }
  | ident as id {
                semicolon := false;
                try Hashtbl.find keywords id
                with Not_found -> semicolon = true;
                    try Hashtbl.find keys_colon id 
                    with Not_found -> IDENT id }
  | eof         { EOF }
  | _           { raise (Lexing_error "Unknown Character" }

and comment1 = parse
  | "*/"  { token lexbuf }
  | "\n"  { new_line token; comment1 lexbuf}
  | _     { comment1 lexbuf }
  | eof   { raise (Lexing_error "Unterminated Comment" )}

and comment2 = parse
  | "\n"  { new_line lexbuf; 
            if !semicolon then semicolon:= false; SEMICOL
            else token lexbuf}
  | _     { comment2 lexbuf }
  | eof   { EOF }