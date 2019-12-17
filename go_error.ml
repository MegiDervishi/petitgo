open Format
open Lexing
open Go_ast

(*Need to create Buffer for strings! *)

exception Typing_error of string * position
exception RequiredTsimpl

let error_msg msg pos = raise (Typing_error (msg,pos))
let notfound_var v_id pos = 
    let msg = sprintf "variable `%s` is not found" v_id in
    error_msg msg pos
let notfound_struct s_id pos = 
    let msg = sprintf "struct `%s` is not found" s_id in 
    error_msg msg pos
let notfound_funct f_id pos =
    let msg = sprintf "function `%s` is not found" f_id in 
    error_msg msg pos
(*let notfound_field field_id pos =
    let msg = sprintf "field `%s` is not found" field_id in 
    error_msg msg pos*)

(* Possible error here: wtf is oc?? *)
let rec print_type oc = function
    |Tint -> Printf.fprintf oc "int";
    |Tbool -> Printf.fprintf oc "bool";
    |Tstring -> Printf.fprintf oc "string";
    |Tstruct s -> Printf.fprintf oc "%s" s;
    |Tstar p -> Printf.fprintf oc "*"; print_type oc p
    |Tnone -> Printf.fprintf oc "none"
    |Tvoid -> Printf.fprintf oc "void" 
                
(*let expected_got t1 t2 pos = 
  let msg = asprintf ("this expression has type `%a` but is expected to have type `%a`")
      print_type t1 
      print_type t2
  in error_msg msg pos*)


let redundant_variable v_id pos = 
  let msg = sprintf "variable with name `%s` is already declared" v_id in 
  error_msg msg pos
let redundant_function f_id pos = 
  let msg = sprintf "function with name `%s` is already declared" f_id in 
  error_msg msg pos
let redundant_struct s_id pos = 
  let msg = sprintf "struct with name `%s` is already declared" s_id in 
  error_msg msg pos
let redundant_field field_id pos = 
  let msg = sprintf "field with name `%s` is already declared" field_id in 
  error_msg msg pos

let leftvalue pos = error_msg  "left value is needed" pos
let cantcomparenil pos = error_msg "can't compare nil with nil" pos
let pointer_missing pos = error_msg  " * requires a pointer declaration" pos
let invalid_return pos = error_msg "you can't return `_`" pos

(*let return_expected t1 t2 pos =
  let msg = asprintf "this function returns a `%a` but is expected to return a `%a`"
       print_type t1 print_type t2
  in error_msg msg pos *)

let invalid_arg pos = error_msg "invalid argument" pos

let localisation_lex ifile pos = 
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:@." !ifile l (c-1) c

let localisation_typer ifile pos =
  let st,e = pos in 
  let l = st.pos_lnum in 
  let start = st.pos_cnum - st.pos_bol + 1 in
  let ends = e.pos_cnum - e.pos_bol +1 in 
      eprintf "File \"%s\", line %d, characters %d-%d:@." !ifile l start ends
