(* Fichier principal du compilateur go *)

open Format
open Lexing


(* Option de compilation, pour s'arrêter à l'issue du parser *)
let parse_only = ref false
let type_only = ref false

(* Noms des fichiers source et cible *)
let ifile = ref ""
let ofile = ref ""

let set_file f s = f := s

(* Les options du compilateur que l'on affiche avec --help *)
let options =
  ["--parse-only", Arg.Set parse_only,
   "  Pour faire uniquement l'analyse syntaxique";
   "--type-only", Arg.Set type_only,
   "  Pour faire uniquement l'analyse syntaxique et le typage"]

let usage = "usage: go [option] file.go"

(* localise une erreur en indiquant la ligne et la colonne *)
let localisation_lex pos = 
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:@." !ifile l (c-1) c

let localisation_typer pos =
  let st,e = pos in 
  let l = st.pos_lnum in 
  let start = st.pos_cnum - st.pos_bol + 1 in
  let ends = e.pos_cnum - e.pos_bol +1 in 
      eprintf "File \"%s\", line %d, characters %d-%d:@." !ifile l start ends

let () =
  (* Parsing de la ligne de commande *)
  Arg.parse options (set_file ifile) usage;

  (* On vérifie que le nom du fichier source a bien été indiqué *)
  if !ifile="" then begin eprintf "Aucun fichier à compiler\n@?"; exit 1 end;
  (* Ce fichier doit avoir l'extension .go *)
  if not (Filename.check_suffix !ifile ".go") then begin
    eprintf "Le fichier d'entrée doit avoir l'extension .go\n@?";
    Arg.usage options usage;
    exit 1
  end;

  if !ofile = "" then 
    ofile := (Filename.remove_extension !ifile);
    let nfile = sprintf "%s.s" !ofile in 

  (* Ouverture du fichier source en lecture *)
  let f = open_in !ifile in

  (* Création d'un tampon d'analyse lexicale *)
  let buf = Lexing.from_channel f in

  try 
    (* Parsing: la fonction  Parser.prog transforme le tampon lexical en un
       arbre de syntaxe abstraite si aucune erreur (lexicale ou syntaxique)
       n'est détectée.
       La fonction Lexer.token est utilisée par Parser.prog pour obtenir
       le prochain token. *)
    let p = Go_parser.program Go_lexer.token buf in
    close_in f;
    print_string "lexing & parsing ok\n";
    (* On s'arrête ici si on ne veut faire que le parsing *)
    if !parse_only then exit 0
    else
    begin
        let env,functions = Go_typer.type_prog p in
        print_string "typage ok\n";
        if !type_only then exit 0
        else
          Compiler.compile_program env nfile;
          exit 0
    end
  with
    | Go_lexer.Lexing_error c ->
      localisation_lex (Lexing.lexeme_start_p buf);
      eprintf "Erreur lexicale: %s@." c;
      exit 1
    | Go_parser.Error ->
      localisation_lex (Lexing.lexeme_start_p buf);
      eprintf "Erreur syntaxique@.";
      exit 1
    | Go_typer.Typing_error (msg, pos) -> 
      localisation_typer pos;
      eprintf "Erreur de typage: %s.@." msg;
      exit 1
    | Go_typer.The_end -> 
      eprintf "the end"; 
      exit 1
    | Go_typer.Unfinished -> eprintf "unfinished"; exit 1
    | Go_typer.Texprweird -> eprintf "Texpr weird"; exit 1
    | Compiler.CompileError -> eprintf "Erreur de compilation"; exit 1
    | _ -> eprintf "Error:weird"; exit 1
