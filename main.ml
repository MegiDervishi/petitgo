(* Fichier principal du compilateur go *)

open Format
open Lexing
open Go_error

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

let usage = "usage: go [option] file.logo"

(* localise une erreur en indiquant la ligne et la colonne *)

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

  (* Ouverture du fichier source en lecture *)
  let f = open_in !ifile in

  (* Création d'un tampon d'analyse lexicale *)
  let buf = Lexing.from_channel f in

  try (
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
        let env,functions = Go_typer.type_prog p in
        print_string "typage ok\n";
        exit 0
  )
    with
    | Go_lexer.Lexing_error c ->
      localisation ifile (Lexing.lexeme_start_p buf);
      eprintf "Erreur lexicale: %s@." c;
      exit 1
    | Go_parser.Error ->
      localisation ifile (Lexing.lexeme_start_p buf);
      eprintf "Erreur syntaxique@.";
      exit 1
    | Go_typer.Typing_error -> 
      localisation ifile (Lexing.lexeme_start_p buf);
      eprintf "Erreur de typage@.";
      exit 1
