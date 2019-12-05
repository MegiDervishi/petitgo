{
open Lexing
open Go_parser

exception Lexing_error of string

let keywords = Hashtbl.create 90
let () = List.iter (fun (s,t) -> Hashtbl.add keywords s t)
    ["else", ELSE; "for", FOR; "func", FUNC; "if", IF; 
    "import", IMPORT;  "package", PACKAGE; "struct", STRUCT;
    "type", TYPE; "var", VAR;]

let keys_colon = Hashtbl.create 4
let () = List.iter (fun (s,t) -> Hashtbl.add keys_colon s t)
      ["true", TRUE;"false", FALSE;"nil", NIL; "return", RETURN;]

let semicolon = ref false;;

let check_semicol lexbuf token_ = Lexing.new_line lexbuf;
	if !semicolon then 
	   begin semicolon := false; SEMICOL end 
	else token_ lexbuf

let check_ident id = 
	try begin semicolon := false; Hashtbl.find keywords id end 
	with Not_found -> semicolon := true;
		try Hashtbl.find keys_colon id
		with Not_found -> (IDENT id)

let check_int64 i =
  try INT ( Int64.of_string i )
  with Failure _ -> raise (Lexing_error (i ^ " is larger than Int64_max"))

}
let letters = ['a'-'z' 'A'-'Z' '_']
let digit = ['0'-'9']
let ident = letters (letters | digit)*

let car = [' ' '!' '#' - '[' ']' - '~'] | "\\\\" | "\\\"" | "\\n" | "\\t"
let strings = "\"" car* "\""

let hexa = ("0x" | "0X") ['0'-'9' 'a'-'f' 'A'-'F']+
let integer = digit+ | hexa
let spaces = [ ' ' '\t' ]

rule token = parse
  | "\n" 		{ check_semicol lexbuf token}
  | spaces+ 		{ token lexbuf }
  | "/*"        	{ comment1 lexbuf }
  | "//"        	{ comment2 lexbuf }
  | "\"fmt\""   	{ semicolon := true; STRING "fmt" }
  | "fmt"       	{ semicolon := true; IDENT "fmt"  }
  | "main"      	{ semicolon := true; IDENT "main" }
  | "Print"     	{ semicolon := true; IDENT "Print"}
  | "&&"        	{ semicolon := false; AND }
  | "||"        	{ semicolon := false; OR }
  | "=="        	{ semicolon := false; ISEQ }
  | "!="        	{ semicolon := false; NEQ }
  | ">"         	{ semicolon := false; GT }
  | ">="        	{ semicolon := false; GEQ }
  | "<"         	{ semicolon := false; LT }
  | "<="        	{ semicolon := false; LEQ }
  | ":="        	{ semicolon := false; REF }
  | "="         	{ semicolon := false; EQUAL}
  | "++"        	{ semicolon := true;  INCR }
  | "--"        	{ semicolon := true;  DECR }
  | "+"         	{ semicolon := false; ADD }
  | "-"         	{ semicolon := false; MINUS }
  | "*"         	{ semicolon := false; MULT }
  | "/"         	{ semicolon := false; DIV }
  | "%"         	{ semicolon := false; MOD }
  | "&"         	{ semicolon := false; ADDRESS }
  | "!"         	{ semicolon := false; NOT }
  | "."         	{ semicolon := false; DOT }
  | "("         	{ semicolon := false; LPAREN }
  | ")"         	{ semicolon := true;  RPAREN }
  | "{"         	{ semicolon := false; LBRACE }
  | "}"         	{ semicolon := true;  RBRACE }
  | ";"         	{ semicolon := false; SEMICOL}
  | ","         	{ semicolon := false; COMMA }
  | integer as i 	{ semicolon := true; check_int64 i}
  | strings as s 	{ semicolon := true; STRING s}
  | ident as id 	{ check_ident id}
  | eof         	{ EOF }
  | _ 		        { raise (Lexing_error "Unknown Character")}

and comment1 = parse
    | "*/" 	{ token lexbuf}
    | "\n" 	{ new_line lexbuf; comment1 lexbuf}
    | _ 	{ comment1 lexbuf}
    | eof 	{ raise (Lexing_error "Unterminated Comment")}

and comment2 = parse
    | "\n" 	{ check_semicol lexbuf token }
    | _ 	{ comment2 lexbuf}
    | eof 	{ raise (Lexing_error "Unterminated Comment")}

