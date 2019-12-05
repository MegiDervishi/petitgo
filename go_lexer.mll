{
  open Lexing
  open Go_parser

  exception LexingError of string

  let keywords = Hashtbl.create 9
  let () = List.iter (fun (s,t) -> Hashtbl.add keywords s t)
      ["else", ELSE; "for", FOR; "func", FUNC; "if", IF; 
      "import", IMPORT;  "package", PACKAGE; "struct", STRUCT;
      "type", TYPE; "var", VAR;]
  let keys_colon = Hashtbl.create 4
  let () = List.iter (fun (s,t) -> Hashtbl.add keys_colon s t)
      ["true", TRUE;"false", FALSE;"nil", NIL; "return", RETURN;]

  let semicolon = ref false;;
}

  let alpha = ['a'-'z' 'A'-'Z' '_']
  let number = ['0'-'9']
  let ident = alpha (alpha | number)*
  let spaces = [ ' ' '\t' ]

  let hexa = ['0'-'9' 'a'-'f' 'A'-'F']
  let entier = number+ | (("0x" "0X") hexa+)

  (*possible error '\'*)
  let car = [' ' '!' '#'-'[' ']'-'~'] |"\\\\"|  "\\\""| "\\n"| "\\t"
  let chaine = "\"" car* "\""

rule token = parse
  | entier as e { semicolon := true; STRING e }
  | "\"fmt\""   { semicolon := true; STRING "fmt" }
  | "main"      { semicolon := true; IDENT "main" }
  | "Print"     { semicolon := true; IDENT "Print"}
  | "fmt"       { semicolon := true; IDENT "fmt"  }
  | chaine as c { semicolon := true; STRING c }
  | "/*"        { comment1 lexbuf }
  | "//"        { comment2 lexbuf }
  | spaces+     { token lexbuf }
  | "\n"        {Lexing.new_line lexbuf;
		            if !semicolon then begin
                semicolon := false;
                SEMICOL
              end else
                token lexbuf}
  | "&&"        { semicolon := false; AND }
  | "||"        { semicolon := false; OR }
  | "=="        { semicolon := false; ISEQ }
  | "!="        { semicolon := false; NEQ }
  | ">"         { semicolon := false; GT }
  | ">="        { semicolon := false; GEQ }
  | "<"         { semicolon := false; LT }
  | "<="        { semicolon := false; LEQ }
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
                with Not_found -> semicolon := true;
                    try Hashtbl.find keys_colon id 
                    with Not_found -> (IDENT id) }
  | eof         { EOF }
  | _           { raise (LexingError "Unknown Character in string: ")}


and comment1 = parse
  | "*/"  { token lexbuf }
  | '\n'  { new_line lexbuf; comment1 lexbuf}
  | _     { comment1 lexbuf }
  | eof   { raise (LexingError "Unterminated Comment" )}

and comment2 = parse
  | "\n"  { new_line lexbuf; 
            if !semicolon then begin semicolon:= false; SEMICOL end 
            else token lexbuf}
  | _     { comment2 lexbuf }
  | eof   { raise (LexingError "Unterminated Comment" ) }
