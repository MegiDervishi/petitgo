open Go_ast
open Format
open X86_64
open Lexing
open Graph

(*

Malloc takes size argument in rdi

Print takes format in rdi and term in rsi (need to zero out al and rax)

the base offset that points to all variables is kept in rbp

All variable are kept track of from Mem[rbp + varnb * 8]

All moving of items is done on rax

*)


exception CompileError

let debugging = true (*Print debug messages or not *)

let dpos = (Lexing.dummy_pos, Lexing.dummy_pos)

let print_debug s =
  (*Print debug messages is flag is on*)
  if debugging then
  begin
    print_string s;
    print_string "\n";
  end

module Smap = Map.Make(String) 

type cstruct = { size : int; fields : int Smap.t; fieldtypes : expr Smap.t}
(*Size of the struct, atribute id -> offset from struct origin,
      atribute id -> type of the atribute.*)

let structs : (ident, cstruct) Hashtbl.t = Hashtbl.create 17

let string_decls : (string, int) Hashtbl.t = Hashtbl.create 17
(* String -> unique string nb. *)

type cvars = {vartable : (ident, int) Hashtbl.t; vartypes : (ident, expr) Hashtbl.t}
(*  Var id -> offset from (rbp),
    Var id -> type of the var,
*)

let vars : cvars = {vartable = Hashtbl.create 17; vartypes = Hashtbl.create 17}

type cfinfo = {input_ids : string list; ret_types : typ list; ret_ofs : (int list) list }
(*
    List of input ids, List of return types,
    List of return offsets (INCOMPLETE).
*)

let func_info : (ident, cfinfo) Hashtbl.t = Hashtbl.create 17

let nil_info : (int list, bool) Hashtbl.t = Hashtbl.create 17
(*
    Offset sequence from (rbp) -> isnil?
*)

let nb_generic_label = ref 0 (* Counter for generic labels *)

let nb_strings = ref 0 (*Counter for the nb of strings in the program *)

let nb_ifelse = ref 0 (*Counter for the nb of if/else conditions in the program *)

let nb_for = ref 0 (*Counter for the nb of for in the program *)

let nb_printbool = ref 0 (*Counter for the nb of bool prints in the program *)

let last_offset = ref 0 (*First free offset from (rbp) *)

let nb_vars = ref 0 (*Total nb of variables in the program*)

let string_var_name id = (sprintf ".StringNb%d" id)
(* Automatic string name generation from string id. *)

let if_var_name id = (sprintf "EndIfNb%d" id)
(* Automatic if/else name generation from if/else id. *)

let else_var_name id = (sprintf "ElseNb%d" id)

let start_for_var_name id = (sprintf "StartForNb%d" id)
(* Automatic for name generation from for id. *)

let end_for_var_name id = (sprintf "EndForNb%d" id)

let rec sizeof = function
  (*  Inputs: 
        - typ
      Outputs:
        - Nb of bytes needed to encode the given typ.
  *)
  | Tnone -> print_debug "Tnone should not be asked for size"; raise CompileError
  | Tvoid -> 0
  | Tstruct s -> 
      (* 
        Struct size are precomputed when they are allocated.
        Furthermore they are the first to be allocated.
      *)
      let cstruct = Hashtbl.find structs s in cstruct.size
  | Tint | Tbool | Tstring | Tstar _ -> 8

let rec sizeof_gt g = match g with 
  (*
      Inputs:
        - gotype = Tmany typ list || Tsimple typ
      Outputs:
        - Nb of bytes needed to encode the full gotype.
  *)
  | Tmany lt -> List.fold_left (fun sum t -> (sizeof t) + sum) 0 lt
  | Tsimpl t -> sizeof t
  | _ -> print_debug "Congratulations! You have done the impossible."; raise CompileError

let length_of_gt g = match g with 
  (*
      Inputs:
        - gotype = Tmany typ list || Tsimple typ
      Outputs:
        - Nb of elements in the gotype.
  *)
  | Tmany lt -> List.length lt
  | Tsimpl t -> 1
  | _ -> print_debug ":'("; raise CompileError

let gotype_to_typlist g = match g with
  (*
      Inputs:
        - gotype = Tmany typ list || Tsimple typ
      Outputs:
        - typ list || [typ]
  *)
  | Tmany lt -> lt
  | Tsimpl t -> [t]
  | _ -> print_debug ":'("; raise CompileError

let rec size_of_types = function
  (*
      Inputs:
        - Type encoded from parser syntax
        (i.e x = ref 5 -> x is of type Eunop(Pointer, Econst(Eint)))
      Outputs:
        - Nb of bytes needed to encode this type.
  *)
  | Econst _ | Eunop(Address, _) | Eunop(Pointer, _) -> 8
  | Eident s -> 
    (* 
      Being of type Eident s corresponds to being the struct s. (var x s;)
    *)
    let cstruct = Hashtbl.find structs s in cstruct.size
  | Eunop(Pointer, e) -> size_of_types (fst e)
  | _ -> print_debug "Unkown size"; raise CompileError

let rec type_to_fmt = function
  (*
      Inputs:
        - type encoded form parser syntax.
      Outputs:
        - Format string needed to print this type. This is a helper function
        for the printing function.
  *)
  | Econst(ENil) -> "<nil>"
  | Econst (Eint64 _) -> "%Ld"
  | Econst (Ebool _) -> "%s"
  | Econst (Estring _) -> "%s"
  | Eunop(Address, (e, _)) -> "%x"
  | Eunop(Pointer, (e, _)) -> "&" ^ (type_to_fmt e)
  | Emethod ((Eident sname, pos), id) -> 
  begin
      let cstruct = Hashtbl.find structs sname in
      type_to_fmt (Smap.find id cstruct.fieldtypes)
  end
  | Eident id -> 
  begin
    try 
    begin
      type_to_fmt (Hashtbl.find vars.vartypes id)
    end
    with Not_found -> raise CompileError
  end
  | Ecall (id, lepos) -> raise CompileError
  | Ebinop (bp, epos1, epos2) -> raise CompileError
  | _ -> print_debug "Type not recognized!"; raise CompileError

let rec typego_to_type tg = 
  (*
      Inputs:
        - typ, pos
      Outputs:
        - Type corresponding to the typ encoded in parser syntax.
      Ex:
        Tmut( Tident "int") -> Eunop(Pointer, Econst(Eint64))
  *)
  let t, pos = tg in  
  match t with
    | Tident "int" -> Econst (Eint64 0L)
    | Tident "string" -> Econst (Estring "\"\"")
    | Tident "bool" -> Econst (Ebool false)
    | Tident s -> Enew([Eident s, dpos])
    | Tmult p -> (*Econst ENil*)
    begin
      let out = typego_to_type p in
      Eunop(Pointer, (out, dpos))
    end
    | Nonetype_go -> Econst ENil
  
let rec typego_to_cmd tg = 
  (*
      Inputs:
        - typ, pos
      Outputs:
        - Command corresponding to typ encoded in parser syntax.
        Note that this is slighly different from a type (reason why
        encoding types this way turned out to be a bad idea.)
      For example:
        x := 1
        y := &x
      Here the *x is the command Eunop(Address, Eident "x") however 
      y is of type Eunop(Pointer, Econst(Eint64)).
  *)
  let t, pos = tg in  
  match t with
    | Tident "int" -> Econst (Eint64 0L)
    | Tident "string" -> Econst (Estring "\"\"")
    | Tident "bool" -> Econst (Ebool false)
    | Tident s -> Eident s
    | Tmult p -> (*Econst ENil*)
    begin
      let out = typego_to_cmd p in
      match out with 
        | Eident s -> Enew([Eident s, dpos])
        | _ -> Eunop(Address, (out, dpos))
    end
    | Nonetype_go -> Econst ENil

let rec extract_strct_name = function
  (*
      Input:
        - type encoded in parser syntax.
      Output:
        - the name of the struct corresponding to the type.
  *)
  | Eident name -> name 
  | Eunop(Pointer, (e, _)) -> (extract_strct_name e)
  | Econst(ENil) -> print_debug "Cannot have nil"; raise CompileError
  | _ -> print_debug "This shouldnt have happened!"; raise CompileError

let rec type_to_string = function
  (*
      Inputs: 
        - type encoded in parser syntax.
      Outputs:
        - string representing the type. This is a function used to help
        debugging.
  *)
  | Econst(ENil) -> "<nil>"
  | Econst(Eint64 _) -> print_debug "Heyho";"Int"
  | Econst(Ebool _) -> "Bool"
  | Econst(Estring _) -> "String"
  | Eunop(Pointer, (e, _)) -> ("&" ^ (type_to_string e))
  | Eunop(Address, (e, _)) -> print_debug "Typing adress"; ("*" ^ (type_to_string e))
  | Eunop(_, (e, _)) -> print_debug "Otehr unop not implemented"; type_to_string e
  | Eprint _ -> print_debug "print shouldn't have been a type"; raise CompileError
  | Emethod ((Eident name, pos), id) -> 
  begin
      print_debug "Typing struct";
      let foo = Hashtbl.find vars.vartypes name in
      let strct_name = extract_strct_name foo in
      let cstruct = Hashtbl.find structs strct_name in
      print_debug "Found cstruct";
      type_to_string (Smap.find id cstruct.fieldtypes)
  end
  | Eident id -> ("{" ^ id ^ "}")
  | Ecall (id, lepos) -> print_debug "Ecall to string not implemented"; raise CompileError
  | Ebinop (bp, epos1, epos2) -> print_debug "Binop to string"; type_to_string (fst epos1)
  | _ -> print_debug "Type not recognized!"; ""

let rec typ_to_expr = function
  (*
      Inputs:
        - typ
      Outputs:
        - type in parser syntax.
  *)
  | Tint -> Econst(Eint64 0L)
  | Tbool -> Econst(Ebool false)
  | Tstring -> Econst(Estring "")
  | Tstruct name -> (Eident name)
  | Tstar t -> (*Econst(ENil)*)
  begin 
    let e = typ_to_expr t in
    Eunop(Pointer, (e, dpos))
  end
  | Tnone -> print_debug "This shouldn't have happened"; raise CompileError
  | Tvoid -> print_debug "This shouldn't have happened"; raise CompileError

let rec typ_to_cmd = function
  (*
      Inputs:
        - typ
      Outputs:
        - command in parser syntax
  *)
  | Tint -> Econst(Eint64 0L)
  | Tbool -> Econst(Ebool false)
  | Tstring -> Econst(Estring "")
  | Tstruct name -> (Eident name)
  | Tstar t -> (*Econst(ENil)*)
  begin 
    let e = typ_to_cmd t in
    match e with
      | Eident s -> Enew([Eident s, dpos])
      | _ -> let e = Eunop(Address, (e, dpos)) in
           print_debug (sprintf "\nHEY HEY HEY: %s\n" (type_to_string e)); e
  end
  | Tnone -> print_debug "This shouldn't have happened"; raise CompileError
  | Tvoid -> print_debug "This shouldn't have happened"; raise CompileError

let alloc_struct strct =
  (*
    Inputs:
      - strct = (Smap id -> typ)
    Outputs:
      - nb bytes needed to encode the struct,
      - Map: attributes id -> offset from the root of the struct
      - Map: attributes id -> attributes type encoded in parser syntax.
  *)
  let size, fields, fieldtypes =
    Smap.fold (fun attr_id attr_typ (size, fields, types) -> 
        print_debug (sprintf "Adding attr %s of type %s" attr_id (type_to_string (typ_to_expr attr_typ)));
        (sizeof attr_typ) + size, Smap.add attr_id size fields,
         Smap.add attr_id (typ_to_expr attr_typ) types)
      strct (0, Smap.empty, Smap.empty)
  in
  { size = size; fields = fields ; fieldtypes = fieldtypes}


(* PART 1: allocation *)

(* Compiler types*)
type cexpr =
  | Cint of int64
  | Cstring of int (* unique int id determined when adding the string to the env*)
  | Cbool of bool
  | Cnil
  | Cstruct of string 
  | Cident of int * string (* Offset from rbp, id*)
  | Cmethod of int list * int * ident * ident 
  (* Sequence of offsets from rbp to get to the parent, 
  Offset of attribute from the parent, 
  parent struct name, attribute name*)
  | Cprint of cexpr list 
  | Cnew of ident
  | Call of ident * int * cexpr list 
  | Cunop of unop * cexpr 
  | Cbinop of binop * cexpr * cexpr

let rec find_lofs l = function
  (*
    Inputs:
      - Initial offset sequence
      - Compiler Expression
    Outputs:
      - Offset sequence required to reach the value
      in memory. [-1] if the expression is not in memory.
    (Partially incomplete)
  *)
  | Cident (ofs, _) -> (l @ [ofs])
  | Cmethod (lsofs, aofs, _, _) -> (l @ lsofs @ [aofs])
  | Cunop(Pointer, ce) -> let fst::out = find_lofs l ce in
                          out
  | Call(fid, retid, lce) -> [-1]
  (*
      INCOMPLETE PART. NEED TO IMPLEMENT
      A WAY TO FIND CALLEE RETURNS OFFSETS.
  *)
  | Cunop(Address, ce) -> let out = find_lofs l ce in 0::out
  | Cbinop(_, ce1, ce2) -> 
  begin
    let out1 = find_lofs l ce1 in 
    let out2 = find_lofs l ce2 in
    match out1, out2 with
      | [-1], [-1] -> [-1]
      | [-1], l -> l
      | l, [-1] -> l
      | l, _ -> l
  end
  | _ -> [-1]

let rec sizeof_ce ce = match ce with 
  (*
      Inputs:
        - Compiler Expression
      Outputs:
        - Nb of bytes needed to encode the expression.
  *)
  | Cint _ | Cstring _ | Cbool _ | Cnil | Cunop(Address, _) | Cunop(Pointer, _) -> 8
  | Cstruct name -> let cstruct = Hashtbl.find structs name in cstruct.size
  | Cident (ofs, id) -> size_of_types (Hashtbl.find vars.vartypes id) 
  | Cmethod (sofs, aofs, sname, aid) -> let cstruct = Hashtbl.find structs sname in 
        size_of_types (Smap.find aid cstruct.fieldtypes)
  | Cnew sname -> let cstruct = Hashtbl.find structs sname in cstruct.size
  | Call _ -> print_debug "Sizeof Call not implemented"; raise CompileError
  | Cunop(Pointer, ce) -> sizeof_ce ce
  | Cbinop _ -> print_debug "Sizeof Binop not implemented"; raise CompileError

let rec print_lofs ?(isstring = false) lofs = 
  (*
    Debugging function to print a sequence of offsets.
  *)
  List.iter(fun ofs -> if isstring then begin print_string (sprintf "%d, " ofs); end
                else begin print_debug (sprintf "%d, " ofs);end) lofs 

let rec get_e_type fid n = function
  (*
      Inputs:
        - Callee function name
        - Index of element required if expression corresponds to multiple values (Call)
        - Command from the parser.
      Outputs:
        The type (encoded in parser syntax) corresponding 
        to the command.
  *)
  | Econst e -> Econst e
  | Eident id -> begin
      let nid = fid ^ "." ^ id in
      print_debug (sprintf "get_e_type: Looking for %s" nid);
      try begin Hashtbl.find vars.vartypes nid end 
      with Not_found -> print_debug (sprintf "Could not find %s so asssigning {%s}" nid id);
                        (Eident id)
  end
  | Emethod((e, _), attr) -> 
  begin
      let rec find_parent l = function
        | Eident name -> (name::l)
        | Emethod (e2, name) -> (find_parent (name :: l) (fst e2))
      in 
      let parent::attrs = find_parent [] e in
      let parent = fid ^ "." ^ parent in
      print_debug (sprintf "Initial parent is %s" parent );
      print_debug "Looking for struct";
      let pt = Hashtbl.find vars.vartypes parent in
      let t = List.fold_left (
        fun p a -> 
              let struct_name = extract_strct_name p in
              print_debug (sprintf "Struct is %s" struct_name);
              print_debug "Looking for cstruct";
              let cstruct = Hashtbl.find structs struct_name in
              print_debug "Found cstruct";
              print_debug "Looking for field type";
              let nt = Smap.find a cstruct.fieldtypes in
              print_debug (sprintf "Field type is %s" (type_to_string nt));
              nt
      ) pt attrs in
      let cstruct = Hashtbl.find structs (extract_strct_name t) in
      Smap.find attr cstruct.fieldtypes
  end
  | Eprint _ -> raise CompileError
  | Enew [(e, _)] -> Eunop(Pointer, (e, dpos))
  | Ecall (id, le_pos) -> 
      let finfo = Hashtbl.find func_info id in
      typ_to_expr (List.nth finfo.ret_types n)
  | Eunop (Address, (e, _)) -> let e2 = (get_e_type fid n e) in
                               Eunop(Pointer, (e2, dpos))
  | Eunop (Pointer, (e, _)) -> print_debug "get_e_type: pointer";
                               let (Eunop(Pointer, (e2,_))) = (get_e_type fid n e) in
                               print_debug (sprintf "Received: %s" (type_to_string e2));
                               e2
  | Ebinop (op, (e1, _), (e2, _)) -> (get_e_type fid n e1)


let rec add_to_nil lofs repeat = function
  (*
      Inputs: 
        - Sequence of offsets of parent
        - Repeat bool (should we look one layer deeper
        e.g. type T struct {x *T}
        When initializing it should we initialize T.x as well?
        )
        - Target expression.
      Outputs:
        Nothing. Adds the sequence of offsets to
        the nil table with the correct value.
  *)
  | Econst ENil -> print_debug "Adding nil to Nil: "; print_lofs lofs; Hashtbl.replace nil_info lofs true
  | Econst _ ->  print_debug "Not adding const to Nil: "; print_lofs lofs; Hashtbl.replace nil_info lofs false
  | Eident s -> 
    begin
      print_debug (sprintf "Adding %s to nil" s); 
      let cstruct = Hashtbl.find structs s in
      Smap.iter (
              fun id ofs -> 
                let t = Smap.find id cstruct.fieldtypes in
                print_debug (sprintf "Attr ofs: %d" ofs);
                let new_l = List.rev lofs in
                let new_l = ofs :: new_l in
                let new_l = List.rev new_l in
                print_debug "Method ofs:";
                print_lofs new_l;
                add_to_nil new_l false t
            ) cstruct.fields
    end
  | Eunop(Pointer, (e, _)) ->  
  begin
      print_debug "Adding pointer to Nil: "; print_lofs lofs; 
      Hashtbl.replace nil_info lofs true;  
      print_debug "Done adding pointer to Nil";
      match e, repeat with
      | Eident sname, true -> add_to_nil lofs false e
      | _ -> ()
  end
  | Eunop _ ->  print_debug "Not Adding unop to Nil: "; print_lofs lofs; Hashtbl.replace nil_info lofs false


let add_var fid id target_e list_id =
  (*
      Inputs:
        - Callee function name
        - Var id
        - Target cmd
        - Index in target if target has multiple values
      Outputs:
        - Offset at which the variable has been saved.
        The function takes care of adding the variable's
        information to the environment.
  *)
  print_debug (sprintf "Processing var %s" id);
  if Hashtbl.mem vars.vartable id then
  begin
    print_debug (sprintf "Var %s already exists" id);
    Hashtbl.find vars.vartable id
  end
  else
  begin
    print_debug (sprintf "Adding var %s" id);
    print_debug "Adding var to table";
    nb_vars := !nb_vars + 1;
    Hashtbl.add vars.vartable id !last_offset;

    let rec add_type_to_table = function
      (*
        Helper function to add the variable to
        vars.vartypes
      *)
      | Econst c -> ( 
          let ofs = Hashtbl.find vars.vartable id in
          match c with
            | Eint64 i -> let t =  (Econst(Eint64 i)) in 
                          add_to_nil [ofs] true t;
                          Hashtbl.add vars.vartypes id t; 
                          8
            | Estring s ->  let t = ( (Econst(Estring s))) in
                            add_to_nil [ofs] true t;
                            Hashtbl.add vars.vartypes id t; 8
            | Ebool b ->  let t = ( (Econst(Ebool b))) in
                          add_to_nil [ofs] true t;
                          Hashtbl.add vars.vartypes id t; 8
            | ENil -> let t =  (Econst ENil)  in
                      add_to_nil [ofs] true t;
                      Hashtbl.add vars.vartypes id t; 8
      )
      | Eident s -> 
      (
        try
        begin
          let ns = fid ^ "." ^ s in
          print_debug (sprintf "Target is ident %s" ns);
          let t = Hashtbl.find vars.vartypes ns in
          let ofs = Hashtbl.find vars.vartable id in
          add_to_nil [ofs] true t;
          Hashtbl.add vars.vartypes id t; (size_of_types t)
        end
        with Not_found -> 
        begin
          (*print_debug "Houston we have a problem!"; raise CompileError *)
          let t = (Eident s) in
          let ofs = Hashtbl.find vars.vartable id in
          Hashtbl.add vars.vartypes id t; 
          add_to_nil [ofs] false t;
          size_of_types t
        end
      )
      | Emethod ((e, pos), attr_id) -> 
        (
          let rec find_parent l = function
            | Eident name -> (name::l)
            | Emethod (e, name) -> (find_parent (name :: l) (fst e))
          in 
          let parent::attrs = find_parent [] e in
          let parent = fid ^ "." ^ parent in
          print_debug "Adding var";
          print_debug (sprintf "Initial parent is %s" parent );
          print_debug "Looking for struct";
          let pt = Hashtbl.find vars.vartypes parent in
          let t = List.fold_left (
            fun p a -> 
                  let struct_name = extract_strct_name p in
                  print_debug (sprintf "Struct is %s" struct_name);
                  print_debug "Looking for cstruct";
                  let cstruct = Hashtbl.find structs struct_name in
                  print_debug "Found cstruct";
                  print_debug "Looking for field type";
                  let nt = Smap.find a cstruct.fieldtypes in
                  print_debug (sprintf "Field type is %s" (type_to_string nt));
                  nt
          ) pt attrs
          in
          let ofs = Hashtbl.find vars.vartable id in 
          add_to_nil [ofs] true t;
          Hashtbl.add vars.vartypes id t;
          size_of_types t
        )
      | Enew [e_pos] -> 
      (
        print_debug "Adding new struct";
        let ofs = Hashtbl.find vars.vartable id in
        match (fst e_pos) with 
        | Eident struct_name -> 
          let t = Eunop(Pointer, (Eident struct_name, dpos)) in
          add_to_nil [ofs] true t;
          Hashtbl.add vars.vartypes id t; 
          size_of_types t
        | _ -> print_debug ". . ."; raise CompileError
      )
      | Ecall (fid2, lepos) -> (print_debug "Allocating call";
                             let finfo = Hashtbl.find func_info fid2 in
                             let t = List.nth finfo.ret_types list_id in
                             let e = (typ_to_expr t) in
                             let ofs = Hashtbl.find vars.vartable id in
                             add_to_nil [ofs] true e;
                             Hashtbl.add vars.vartypes id e;
                             sizeof t)
      | Eunop (op, (e,p)) -> (
        print_debug "Adding unop";
          let t = get_e_type fid 0 (Eunop(op, (e, p))) in 
          print_debug (sprintf "Computed type is: %s" (type_to_string t));
          let ofs = Hashtbl.find vars.vartable id in
          add_to_nil [ofs] true t;
          print_debug "Added nil";
          Hashtbl.add vars.vartypes id t;
          print_debug (sprintf "Added unop to id %s" id);
          (size_of_types t)
      )
      | Ebinop (bp, e1, e2) -> add_type_to_table (fst e1)
      | _ -> print_debug "This shouldn't happen!"; raise CompileError
    in
    print_debug "Adding type to table";
    let size = add_type_to_table target_e in
    print_debug (sprintf "Done adding %s of size %d"
               id size );
    print_debug (sprintf "Previous last offset was %d" !last_offset);
    last_offset := !last_offset + size;
    print_debug (sprintf "Last offset is %d" !last_offset);
    !last_offset - size
  end

let reserve_var = function
  (*
    Reserve an empty space in memory for a future var.
  *)
  | Cint _ | Cstring _ | Cbool _ -> print_debug "Reserving space for int";
    let offset = !last_offset in
    last_offset := offset + 8;
    offset
  | Cstruct name ->
    print_debug (sprintf "Reserving space for struct %s" name);
    let offset = !last_offset in
    let cstruct = Hashtbl.find structs name in
    last_offset := offset + cstruct.size;
    offset

let add_string s = 
  (*
    Input: 
      - String s
    Output:
      - Compiler expression corresponding to the string.
      The function also takes care of the id being unique.
  *)
  if Hashtbl.mem string_decls s then
  begin
    let tbl_id = Hashtbl.find string_decls s in
    print_debug (sprintf "String %s is already declared" s);
    Cstring tbl_id
  end
  else
  begin
    nb_strings := !nb_strings + 1;
    print_debug (sprintf "Adding to table string %s with value %d" s !nb_strings);
    Hashtbl.add string_decls s !nb_strings;
    Cstring !nb_strings
  end
  
let compile_string cs = match cs with
  (*
    Input:
      - Compiler String
    Output:
      x86 code to print the string.
  *)
  |Cstring id -> movq (ilab (string_var_name id)) !%rdi ++
            xorq !%rax !%rax ++
            xorb !%al !%al ++ 
            call "printf"
  | _ -> raise (CompileError)


let put_blank = (compile_string (Cstring (0)))
(* x86 code to put a blank *)

let rec process_method fid id = function
  (*
    Inputs: 
      - Callee function name
      - Attribute name
      - Parent of Method.
    Outputs:
      Compiler expression of the method. The function
      takes care of computing the sequence of offsets 
      from rbp to reach the parent and finally the 
      offset of the attribute from the parent.
  *)
  | Eident parent, _ -> 
  begin
    print_debug (sprintf "Processing %s.%s" (fid ^"."^ parent) id);
    try begin
      print_debug "Looking for parent var";
      let offset = Hashtbl.find vars.vartable (fid ^ "." ^ parent) in
      print_debug "Found Parent Var. Looking for Parent Structure";
      let foo = Hashtbl.find vars.vartypes (fid ^ "." ^ parent) in
      print_debug (sprintf "Try: %s" (type_to_string foo));
      let strc_name = extract_strct_name foo in
      print_debug "Found Parent Structure Looking for Structure";
      let cstruct = Hashtbl.find structs strc_name in
      Cmethod ([offset], Smap.find id cstruct.fields, strc_name, id)
      end
    with Not_found -> print_debug (sprintf "Did not find parent %s of %s" parent id);raise CompileError 
  end
  | Emethod (pe, id2), _ -> 
    let Cmethod (lparent_offset, attr_offset, prev_strc, prev_attr) = process_method fid id2 pe in
    let offset = lparent_offset @ [attr_offset] in
    let prev_cstruct = Hashtbl.find structs prev_strc in
    let foo = Smap.find prev_attr prev_cstruct.fieldtypes in
    let type_prev_attr = extract_strct_name foo in
    let cstruct = Hashtbl.find structs type_prev_attr in
    Cmethod (offset, Smap.find id cstruct.fields, type_prev_attr, id)
  | _ -> print_debug "Parent strucutre should be an ident or method";raise CompileError

let rec alloc_expr fid is_type = function 
  (*
    Inputs:
      - Callee function name
      - Is passed argument a type or command?
      - Parser Argument
    Outputs:
      Compiler Expression. 
  *)
  | Econst c -> begin match c with 
      | Eint64 i -> Cint i
      | Estring s -> begin
        print_debug (sprintf "Processing string %s" s);
        add_string s
      end
      | Ebool b -> Cbool b
      | ENil -> Cnil end
  | Eident id -> 
  begin
    try
    begin
      let id = fid ^ "." ^ id in
      print_debug (sprintf "alloc_expr:Looking for %s" id);
      print_debug "Searching for offset";
      let offset = Hashtbl.find vars.vartable id in
      print_debug (sprintf "Found offset: %d" offset);
      Cident (offset, id)
    end
    with Not_found -> 
    print_debug "Allocating Cstruct"; Cstruct id
  end
  | Emethod (pe, id) -> 
    process_method fid id pe
  | Eprint (le_pos) -> 
      print_debug "Allocating print";
      let ces =
        List.fold_left
          (fun l e -> 
            let expr = (alloc_expr fid false (fst e)) in
            match expr with
              | Call(fid, _, lce) ->
                let finfo = Hashtbl.find func_info fid in
                let tl,_ = List.fold_left(
                  fun (l, cnt) typ -> (Call(fid, cnt, lce)::l, cnt + 1)
                ) ([], 0) finfo.ret_types in
                tl @ l
              | _ -> expr :: l
          ) [] le_pos
      in
      print_debug "Finished Allocating Print";
      Cprint ces
  | Enew [e_pos] -> 
  begin 
    match e_pos with
      | Eident struct_name, _ -> Cnew struct_name
      | _ -> raise(CompileError)
  end
  | Enew _ -> print_debug "weird should have failed at parser"; raise (CompileError)
  | Ecall (id, le_pos) -> 
  (*
    For future use a function call is split
    into different compiler expression corresponding
    to the disting return values.
  *)
  begin
      print_debug (sprintf "Allocating call to %s" id);
      let ces =
        List.fold_left
          (fun l e -> 
            let expr = (alloc_expr fid false (fst e)) in
            match expr with
              | Call(fid, _, lce) -> 
                let finfo = Hashtbl.find func_info fid in
                let tl,_ = List.fold_left(
                  fun (l, cnt) typ -> (Call(fid, cnt, lce)::l, cnt + 1)
                ) ([], 0) finfo.ret_types in
                tl @ l
              | _ -> expr::l
          ) [] le_pos
      in
      print_debug (sprintf "Done allocating call to %s" id);
      Call (id, -1, ces)
  end
  | Ebinop (op, (e1, p1), (e2,p2)) -> 
        let e1 = alloc_expr fid false e1 in
        let e2 = alloc_expr fid false e2 in 
        Cbinop(op, e1, e2)
  | Eunop (op, e) -> 
  begin
    match is_type with
      | true -> Cnil
      | false -> let ce = alloc_expr fid false (fst e) in Cunop (op, ce)
  end

type cinstruction =
| Cnilinstr
| Cexpr         of cexpr
| Cblock        of cinstruction list
| Cfor          of cexpr * cinstruction
| Cif           of cexpr * cinstruction * cinstruction
| CAssign_List  of cexpr list * cexpr list
| Cvar          of ident list * expr * cexpr list
| Cref          of ident list * cexpr list * bool
| Creturn       of cexpr list

let rec alloc_instr fid = function
  (*
    Inputs:
      - Callee function name
      - Parser instruction
    Outputs:
      Compiler instruction.
  *)
  | Inil -> Cnilinstr
  | Iinstrsimpl (instr, pos_instr) -> begin
    match instr with 
      | Isexpr (e, pose) -> let ce = alloc_expr fid false e in Cexpr ce
      | Isassign_incdec ((e,_), (adde, _)) -> 
        let ce = alloc_expr fid false e in
        let ce2 = alloc_expr fid false adde in
        CAssign_List([ce], [ce2]) 
      | Isassign_list (le1, le2) ->
      begin
        let lce1 = List.fold_left (fun l e -> (alloc_expr fid false (fst e)) :: l) [] le1 in
        let lce1 = List.rev lce1 in
        let lce2 = List.fold_left (
          fun l e -> let expr = (alloc_expr fid false (fst e)) in
                     match expr with
                        | Call(fid, _, lce) ->
                          let finfo = Hashtbl.find func_info fid in
                          let lt, _ = List.fold_left (
                            fun (l, cnt) _ -> (Call(fid, cnt, lce)::l, cnt+1)
                          ) ([], 0) finfo.ret_types in
                          lt @ l
                        | _ -> expr :: l
        ) [] le2 in
        CAssign_List (lce1, lce2)
      end
      | Isref (lid, le) -> 
      begin
        let lid = List.fold_left (fun tl id -> (fid ^ "." ^ id) :: tl) [] lid in
        let lid = List.rev lid in
        let lce, _ = List.fold_left (fun (l1, cnt) e -> 
              let ce = alloc_expr fid false (fst e) in
              match ce with
                | Call(fid, _, lce) ->  
                  let finfo = Hashtbl.find func_info fid in
                  let lt, retnb = List.fold_left (
                    fun (l, retid) _ -> 
                      let id = List.nth lid (cnt  +retid) in
                      print_debug (sprintf "isref: allocating to %s from function" id);
                      let foo = add_var fid id (fst e) retid in
                      print_debug (sprintf "Added var from function output! With retid: %d" retid);
                      (Call(fid, retid, lce) :: l, retid + 1)
                  ) ([], 0) finfo.ret_types in
                  (lt @ l1, cnt + retnb)
                | _ -> 
                  let id = List.nth lid cnt in
                  print_debug (sprintf "isref: allocating to %s" id); 
                  let foo = add_var fid id (fst e) cnt in
                  print_debug (sprintf "Current last offset of %s is %d" id !last_offset);
                  print_debug (sprintf "Done allocating var %s of type %s in position %d\n" id 
                    (type_to_string(Hashtbl.find vars.vartypes id)) foo );
                  (ce :: l1), (cnt+1)
              )
          ([], 0) le in
        Cref (lid, lce, true)
      end
      | _ -> print_debug "This shouldn't happen\n"; raise CompileError;
    end
  | Iblock bp -> 
      print_debug "alloc block\n";
      let cis =
       List.fold_left
         (fun cis e_pos ->
           let ce = alloc_instr fid (fst e_pos) in
           ce :: cis) [] (fst bp)
     in
     Cblock (List.rev cis)
  | Iif (((e, pose), b1, b2), posif) -> 
    let ce = alloc_expr fid false e in
    let cinstr1 = alloc_instr fid (Iblock b1) in
    let cinstr2 = alloc_instr fid (Iblock b2) in
    Cif(ce, cinstr1, cinstr2)
  | Ivar (lid, tgpos, []) -> print_debug "Uninitialized vars"; 
        let lid = List.fold_left (fun tl id -> (fid ^ "." ^ id) :: tl) [] lid in
        let t = typego_to_cmd tgpos in
        print_debug (sprintf "Hey default command is: %s" (type_to_string t));
        List.iteri (
          fun cnt id -> 
            let foo = add_var fid id t cnt in ()
        ) lid;
        let lce = List.fold_left (fun l _ -> (alloc_expr fid false t) :: l) [] lid in
        Cref (lid, lce, false)
  | Ivar (lid, tgpos, lepos)  -> 
      let t = match tgpos with
        | Nonetype_go, _ -> (fst (List.hd lepos))
        | _ -> typego_to_cmd tgpos
      in
      let lid = List.fold_left (fun tl id -> (fid ^ "." ^ id) :: tl) [] lid in
      let lce, _ = List.fold_left (
        fun (l, cnt) e ->
          let ce = alloc_expr fid false (fst e) in
          match ce with
            | Call(fid, _, lce) -> 
                print_debug "Assigning (var) from function returns";
                let finfo = Hashtbl.find func_info fid in
                let lt, retnb = List.fold_left (
                  fun (lt, retid) _ -> 
                    let id = List.nth lid (cnt+retid) in
                    print_debug (sprintf "Assigning var %s (function)" id);
                    let foo = add_var fid id t retid in
                    print_debug (sprintf "Done allocating %s from function return" id);
                    (Call(fid, retid, lce) :: lt, retid + 1)
                ) ([], 0) finfo.ret_types in
                (lt @ l, cnt + retnb)
            | _ -> 
                let id = List.nth lid cnt in
                print_debug (sprintf "Assigning var %s" id);
                let foo = add_var fid id t cnt in
                print_debug (sprintf "Current last offset is %d" !last_offset);
                print_debug (sprintf "Done allocating var %s of type %s in position %d\n" id 
                  (type_to_string (Hashtbl.find vars.vartypes id)) foo );
                (ce::l, cnt + 1)) 
      ([], 0) lepos in
      Cref (lid, lce, true)
  | Ireturn lepos ->  
      let finfo = Hashtbl.find func_info fid in
      let lce, retofs = List.fold_left (
          fun (l, retofs) e -> 
            let expr = (alloc_expr fid false (fst e)) in
            match expr with
              | Call(fid2, _, lce2) ->
                let finfo2 = Hashtbl.find func_info fid2 in
                let tl,_ = List.fold_left(
                  fun (l, cnt) typ -> (Call(fid2, cnt, lce2)::l, cnt + 1)
                ) ([], 0) finfo2.ret_types in
                let newofs = find_lofs [] expr in
                print_lofs newofs;
                ((List.rev tl) @ l, newofs::retofs)
              | _ -> 
                print_debug "looking for ret ofs";
                let newofs = find_lofs [] expr in
                print_lofs newofs;
                expr :: l, newofs :: retofs
        ) ([],[]) lepos in 
        print_debug "---------------\n Adding retinfo \n -----------------------";
        let newfinfo = {input_ids = finfo.input_ids; ret_types = finfo.ret_types; ret_ofs = retofs} in
        Hashtbl.replace func_info fid newfinfo;
        Creturn lce
  | Ifor ((e, pose), b) -> 
    let ce = alloc_expr fid false e in
    let cinstr = alloc_instr fid (Iblock b) in
    Cfor(ce, cinstr)
  | _ -> print_debug "This shouldn't happen\n"; raise CompileError

let alloc env =
  (*
    Main allocation function.
      Inputs:
        - Typer environment.
      Outputs:
        - List of compiler instructions to be passed to the
        compiler.
  *)
  (* allocating structs*)
  print_debug "Alloc function start";
  Smap.iter
    (fun struc_id struc_map ->
      let cs = alloc_struct struc_map in
      let cs = {size = cs.size; fields = cs.fields; fieldtypes = cs.fieldtypes} in
      Hashtbl.add structs struc_id cs) env.structs;
      
  (* allocating function headers (names and inputs)*)
  Smap.iter
    (fun fid (input_vars, body) ->
      print_debug (sprintf "Initializing %s\n" fid); 
      let _, ret = Smap.find fid env.funct in
      print_debug (sprintf "Found %s in env\n" fid);
      print_debug (sprintf "Adding %s info" fid);
      Hashtbl.add func_info 
          fid
          {input_ids = List.fold_left (fun l (id, typ) -> (fid ^ "." ^ id) :: l) [] input_vars;
            ret_types = gotype_to_typlist ret; ret_ofs = []};
      print_debug (sprintf "Adding input vars of %s" fid);
      List.iteri (fun cnt (id, typ) -> 
        let foo = add_var fid (fid ^ "." ^ id) (typ_to_cmd typ) cnt in
        Hashtbl.replace nil_info [foo] false; ()) input_vars;)
    env.funct_info;

  (* Allocating function bodies. *)
  Smap.mapi
    (fun fid (input_vars, body) ->
      print_debug (sprintf "\nAllocating body of %s\n" fid);
      let cast = alloc_instr fid body in
      cast)
    env.funct_info


let go_to_end_method lofs regin regout = 
  (*
    Helper function that produces x86 code
    to navigate to the end of a method.
  *)
  let fofs::rofs = lofs in
  List.fold_left (fun cmd ofs -> cmd ++ movq (ind ~ofs:ofs regin) regout) (movq (ind ~ofs:fofs rbp) regout) rofs


(* PART 2: machine code *)
let rec compile_binop = function
  (*
    Inputs:
      - Binop
    Outputs:
      - x86 code to apply Binop(rbx, rax)
  *)
  | Add -> addq !%rbx !%rax
  | Minus -> subq !%rbx !%rax
  | Mult -> imulq !%rbx !%rax
  | Div -> cqto ++ idivq !%rbx
  | Mod -> cqto ++ idivq !%rbx ++ movq !%rdx !%rax
  | Iseq -> cmpq !%rbx !%rax ++ sete !%al
  | Neq -> cmpq !%rbx !%rax ++ setne !%al
  | Lt -> cmpq !%rbx !%rax ++ setl !%al
  | Leq -> cmpq !%rbx !%rax ++ setle !%al
  | Gt -> cmpq !%rbx !%rax ++ setg !%al
  | Geq -> cmpq !%rbx !%rax ++ setge !%al
  | And -> andq !%rbx !%rax
  | Or -> orq !%rbx !%rax

and compile_unop = function
  (*
    Inputs:
      - unop
    Outputs:
      - x86 code for Unop(rax)
  *)
  | Not -> testq !%rax !%rax ++ sete !%al
  | Address -> movq (ind rax) !%rax
  | Pointer -> nop
  | Sign -> nop

and type_ce = function
  (*
    Inputs: 
      - Compiler Expression
    Outputs:
      - Type corresponding to the expression in parser syntax.
  *)
  | Cnil -> (Econst ENil)
  | Cint _ -> (Econst (Eint64 0L))
  | Cbool _ -> (Econst (Ebool false))
  | Cstring _ -> (Econst (Estring ""))
  | Cstruct s -> (Eident s)
  | Cident (ofs, id) -> 
  begin
    print_debug "Looking for var type";
    let t = Hashtbl.find vars.vartypes id in
    print_debug (sprintf "Found var type: %s" (type_to_string t));
    match t with 
      | Eunop(Pointer, _) -> print_debug (sprintf "hey looking for: %d" ofs); 
          if Hashtbl.find nil_info [ofs] then (Econst ENil) else t
      | _ -> t 
  end
  | Cmethod (lsofs, aofs, strc, attr) -> 
  begin
    print_debug (sprintf "Finding type of method %s.%s" strc attr);
    print_debug (sprintf "Looking for struct info of %s" strc);
    let cstruct = Hashtbl.find structs strc in
    print_debug "Found struct info";
    let t = Smap.find attr cstruct.fieldtypes in
    print_debug (sprintf "Found type: %s" (type_to_string t));
    print_lofs lsofs;
    print_debug (sprintf "%d" aofs);
    let lofs = lsofs @ [aofs] in
    print_debug "Looking for ofs:";
    print_lofs lofs;
    let b = Hashtbl.find nil_info lofs in
    print_debug "Found nil info";
    match t with
      | Eunop(Pointer, _) -> if b then (Econst ENil) else t
      | _ -> t
  end
  | Cprint _ -> raise CompileError
  | Cnew s -> Eunop(Pointer, (Eident s, dpos))
  | Call (fid, retid, _) -> let finfo = Hashtbl.find func_info fid in
                  typ_to_expr (List.nth finfo.ret_types retid)
  | Cbinop(op, ce1, ce2) -> type_ce ce1
  | Cunop(Pointer, cep) -> print_debug "typing pointer";
                           let t = type_ce cep in
                           print_debug (sprintf "found type %s" (type_to_string t));
                           let (Eunop(Pointer, (e,_))) = type_ce cep in e
  | Cunop(Address, cep) -> Eunop(Pointer, (type_ce cep, dpos))

and compile_expr = function
  (*
    Inputs:
      - Compiler expression.
    Outputs:
      - x86 code corresponding to the expression that
      returns the expression to rax.
  *)
  | Cnil -> xorq !%rax !%rax
  | Cint i -> print_debug (sprintf "Int: %Ld" i); movq (imm64 i) !%rax
  | Cbool true -> movq (imm64 1L) !%rax ++ movb (imm64 1L) !%al
  | Cbool false -> xorq !%rax !%rax ++ xorb !%al !%al
  | Cstring c -> movq (ilab (string_var_name c)) !%rax 
  | Cident (offset, id) -> movq (ind ~ofs:offset rbp) !%rax
  | Cstruct sname -> 
  begin
    print_debug "Compiling Cstruct";
    let cstruct = Hashtbl.find structs sname in
    let cmd = comment"Compiling Cstruct" ++ 
              movq (ilab (Int.to_string cstruct.size) ) !%rdi ++ 
              call "malloc" ++
              movq !%rax !%r13 in
    print_debug "Found all base values";
    let cmd = Smap.fold (
      fun id ofs c -> let e = Smap.find id cstruct.fieldtypes in
                      let ce = alloc_expr "" true e in
                      c ++
                      compile_expr ce ++
                      movq !%rax (ind ~ofs:(ofs) r13)            
    ) cstruct.fields cmd in
    cmd ++ movq !%r13 !%rax
  end
  | Cbinop(op, e1, e2) when op = And || op = Or ->
      let genLabel = (sprintf "\"GenLabelNb%d\"" !nb_generic_label) in
      nb_generic_label := !nb_generic_label + 1;
       compile_expr e1 ++
       xorq (imm64 0L) !%rax ++
       (if op = Or then jne else je) genLabel ++
       compile_expr e2 ++
       label genLabel
  | Cbinop (op, e1, e2) ->
     comment"binop" ++
       compile_expr e2 ++
       pushq !%rax ++
       compile_expr e1 ++
       popq rbx ++
       compile_binop op
  | Cunop (op, ce) -> 
  begin
    print_debug "Compiling unop";
    match op with 
      | Address -> 
      begin
        print_debug "Compiling address";
        match ce with
          | Cident (offset, id) -> leaq (ind ~ofs:offset rbp) rax
          | Cmethod (lsofs, aofs, strc, attr) -> 
                  go_to_end_method lsofs rax !%rax ++
                  leaq (ind ~ofs:aofs rax) rax
          | Cunop (Pointer, ce2) ->  compile_expr ce2
      end
      | Pointer ->
      begin
      print_debug "Compiling pointer";
        match ce with 
          | Cident (offset, id) ->  comment"Compiling Pointer of Ident" ++ 
                                    compile_expr ce ++
                                    movq (ind rax) !%rax 
          | Cmethod (lsofs, aofs, strc, attr) ->
                            comment"Compiling pointer of Method" ++
                            compile_expr ce ++
                            movq (ind rax) !%rax
          | Cstruct sname -> print_debug "Compiling pointer of struct";
                            comment"Compiling pointer of struct" ++
                            compile_expr ce ++
                            movq (ind rax) !%rax
          | Cunop (Address, ce2) -> compile_expr ce2
          | _ -> print_debug "This shouldn't happen"; raise CompileError
      end
      | Not -> print_debug "Not not implemented :P"; nop
      | Sign -> print_debug "Sign not implemented"; nop
      | _ -> print_debug "Weird unop"; nop
  end
  | Cmethod (lsofs, aofs, strc, attr) -> 
  begin
    let t = type_ce (Cmethod (lsofs, aofs, strc, attr)) in
    match t with
      | Econst(ENil) -> compile_expr Cnil
      | _ ->  go_to_end_method lsofs rax !%rax ++
              movq (ind ~ofs:aofs rax) !%rax
  end
  | Cprint (lce) -> 
  begin
  let print_struct lofs sname = 
    (*
      Inputs:
        - Sequence of offsets to reach struct
        - Struct name
      Outputs:
        - x86 code to print the struct and all
        of it's attributes.
    *)
    let cstruct = Hashtbl.find structs sname in
    let cs1 = add_string "\"{\"" in
    let cs2 = add_string "\"}\"" in
    let cstruct = Hashtbl.find structs sname in
    let fofs::rofs = lofs in
    compile_string cs1 ++
    comment"Retrieving class offset" ++
    List.fold_left (
      fun c ofs -> c ++ movq (ind ~ofs:ofs r14) !%r14
    ) (movq (ind ~ofs:fofs rbp) !%r14) rofs ++
    comment"Found class offset, printing attributes" ++
    Smap.fold (
            fun aid aofs c -> 
              let t = Smap.find aid cstruct.fieldtypes in
              let fmt = "\" " ^ (type_to_fmt t) ^ "\"" in
              let Cstring fmt_id = add_string fmt in
              c ++
              comment(sprintf "Printing attribute %s" aid) ++
              movq (ilab (string_var_name fmt_id)) !%rdi ++
              movq (ind ~ofs:aofs r14) !%rsi ++
              xorq !%rax !%rax ++
              xorb !%al !%al ++
              call "printf"
          ) cstruct.fields nop ++
    xorq !%r14 !%r14 ++
    compile_string cs2
  in
  let rec printing_helper prev_is_string cmd pname = function
    (*
      Inputs:
        - Is previous printed element a string?
        - List of x86 instructions.
        - Name of the previous expression.
        - List of compiler expressions.
      Outputs:
        - x86 code to print the given compiler expresions.
    *)
    | [] -> cmd
    | ce::l -> 
    begin 
      print_debug "Looking for element type";
      let e = type_ce ce in
      print_debug "Done typing ce";
      print_debug (sprintf "Printing element of type %s" (type_to_string e));
      match e with
        | Econst(ENil) -> let cs = add_string "\"<nil>\"" in
                  if prev_is_string then printing_helper false ((compile_string cs) ++ cmd) pname l
                  else printing_helper false ((compile_string cs) ++ put_blank ++ cmd) pname l
        | Eident sname -> 
        begin
          print_debug "Printing a struct";
          let cstruct = Hashtbl.find structs sname in
          let lofs = find_lofs [] ce in
          let cs1 = add_string "\"{\"" in
          let cs2 = add_string "\"}\"" in
          let cs3 = add_string "\" \"" in
          let subprint = Smap.fold (
            fun id ofs sl -> cs3::(Cmethod(lofs, ofs, sname, id) :: sl)
          ) cstruct.fields [cs1] in
          let _::subprint = subprint in
          let subprint = (cs2::subprint) in
          printing_helper prev_is_string cmd pname (subprint @ l)
        end
        | Eunop(Pointer, (Eident sname, _)) -> 
        begin
          print_debug "Printing a struct pointer";
          let cstruct = Hashtbl.find structs sname in
          let lofs = find_lofs [] ce in
          let cs1 = add_string "\"&{\"" in
          let cs2 = add_string "\"}\"" in
          let cs3 = add_string "\" \"" in
          let subprint = Smap.fold (
            fun id ofs sl -> cs3::(Cmethod(lofs, ofs, sname, id) :: sl)
          ) cstruct.fields [cs1] in
          let _::subprint = subprint in
          let subprint = (cs2::subprint) in
          printing_helper prev_is_string cmd pname (subprint @ l)
        end
        | Econst(Ebool _) -> 
          let ts = add_string "\"true\"" in
          let fs = add_string "\"false\"" in
          nb_printbool := !nb_printbool + 1;
          let newcmd = 
            compile_expr ce ++
            movq (imm64 0L) !%rbx ++
            cmpq !%rax !%rbx ++
            je (sprintf "PrintFalseNb%d" !nb_printbool) ++
            compile_string ts ++
            jmp (sprintf "EndFalseNb%d" !nb_printbool) ++
            label (sprintf "PrintFalseNb%d" !nb_printbool) ++
            compile_string fs ++
            label (sprintf "EndFalseNb%d" !nb_printbool)
          in
          if prev_is_string then printing_helper false (newcmd ++ cmd) pname l 
          else printing_helper false (newcmd ++ put_blank ++ cmd) pname l
        | Econst(Estring _) ->
          let fmt = "\"%s\"" in
          let Cstring fmt_id = add_string fmt in
          let newcmd = 
            comment(sprintf "Printing standard type %s" (type_to_string e)) ++
            compile_expr ce ++
            movq (ilab (string_var_name fmt_id)) !%rdi ++
            movq !%rax !%rsi ++ 
            xorq !%rax !%rax ++
            xorb !%al !%al ++
            call "printf" in
          printing_helper true (newcmd ++ cmd) pname l
        | _ as e ->
        begin
          print_debug (sprintf "Printing standard type %s" (type_to_string e));
          let fmt = (sprintf "%S" (type_to_fmt e)) in
          print_debug "Found fmt";
          let Cstring fmt_id = add_string fmt in
          print_debug "Done with format, making command";
          let newcmd = 
          comment(sprintf "Printing standard type %s" (type_to_string e)) ++
          compile_expr ce ++
          movq (ilab (string_var_name fmt_id)) !%rdi ++
          movq !%rax !%rsi ++ 
          xorq !%rax !%rax ++
          xorb !%al !%al ++
          call "printf" in
          print_debug "Done compiling print of this element";
          if prev_is_string then printing_helper false (newcmd ++ cmd) pname l
          else printing_helper false (newcmd ++ put_blank ++ cmd) pname l
        end
    end
  in
    printing_helper true nop "" lce
  end
  | Cnew strct_name -> 
  begin 
    let cstruct = Hashtbl.find structs strct_name in
    movq (ilab (Int.to_string cstruct.size)) !%rdi ++
    call "malloc"
  end
  | Call (id, -1, lce) -> 
    (* 
      Call a function:
        Save all callee saved registers: rbp, rbx, r12, r13, r14
        Copy all of the variables to a new environment that will 
        be passed to the function.
        Call to the function
        Unpacking of the return values to rcx
        Restoring the registers.
    *)
                      print_debug "Compiling call";
                      let callee_saved_regs = [rbp; rbx; r12; r13; r14] in
                      print_debug (sprintf "Looking for finfo of: %s" id);
                      let finfo = Hashtbl.find func_info id in
                      print_debug "Found finfo";
                      let ret_size, lofs = List.fold_left (
                        fun (cnt, l) typ -> (cnt + (sizeof typ), cnt::l)
                      ) (0, []) finfo.ret_types in
                      let lofs = List.rev lofs in
                      print_debug "Done with precomputations";
                      let savecmd = comment"Saving regs" ++
                      List.fold_left (
                        fun cmd reg -> cmd ++ pushq !%reg 
                      ) nop callee_saved_regs in
                      let copycmd = comment"Re-creating environment" ++
                      movq (ilab (Int.to_string ((!nb_vars+1) * 8))) !%rdi ++
                      call "malloc" ++
                      Hashtbl.fold(
                        fun _ ofs cmd -> cmd ++ movq (ind ~ofs:ofs rbp) !%r12 ++ movq !%r12 (ind ~ofs:ofs rax)
                      ) vars.vartable nop ++
                      movq !%rax !%rbp ++
                      comment"Finished cloning environment" in
                      let inputcmd =
                      List.fold_left (fun cmd ce -> comment"Compiling inputs" ++
                                                    compile_expr ce ++
                                                    pushq !%rax ++ cmd ) nop (lce) ++
                      call id in
                      let returncmd = comment"Allocating space for returned values" ++
                      movq (ilab (Int.to_string ret_size )) !%rdi ++
                      call "malloc" in
                      let unpackcmd = 
                      comment"Unpacking return values" ++ 
                      List.fold_left (
                        fun cmd ofs -> cmd ++ popq (sprintf "%d(%%rax)" ofs)
                      ) nop lofs ++
                      movq !%rax !%rcx ++
                      movq (ind rax) !%rax in
                      let restorecmd = 
                      comment"Restoring regs" ++
                      List.fold_left (
                        fun cmd reg -> popq reg ++ cmd
                      ) nop callee_saved_regs in
                      print_debug (sprintf "Finished compiling function call to: %s" id);
                      savecmd ++ copycmd ++ inputcmd ++ returncmd ++ unpackcmd ++ restorecmd
  | Call(fid, 0, lce) -> 
    (* Calling and retreiving the first result *)
    compile_expr (Call(fid, -1, lce)) ++
    movq (ind rcx) !%rax 
  | Call(fid, retid, lce) -> 
    (* Retreiving the retid result *)
    print_debug (sprintf "Compiling call with retid: %d" retid);
    let finfo = Hashtbl.find func_info fid in
    let lofs, _ = List.fold_left (
      fun (l, s) typ -> (s :: l, (sizeof typ) + s)
    ) ([], 0) finfo.ret_types in
    let lofs = List.rev lofs in
    print_lofs lofs;
    let ofs = List.nth lofs retid in
    print_debug (sprintf "Found ofs to be: %d" ofs);
    movq (ind ~ofs:(List.nth lofs retid) rcx) !%rax 
  | _ -> print_debug "Missing something"; raise CompileError

and is_nil = function
  (*
    Inputs:
      - Compiler Expression
    Outputs:
      Bool, wether the compiler expression is nil or not.
  *)
  | Cint _ | Cstring _ | Cbool _ | Cnew _ | Cbinop _ -> false
  | Cnil -> true
  | Cident (ofs, id) -> print_debug (sprintf "Looking for nil info of: %d, %s" ofs id);
                        Hashtbl.find nil_info [ofs] 
  | Cmethod (lsofs, aofs, _, _) -> let lofs = lsofs @ [aofs] in print_lofs lofs;
    Hashtbl.find nil_info lofs
  | Cunop(Pointer, ce) -> is_nil ce
  | Cunop _ -> false
  | Call _ -> print_debug "Nil checking for functions not implemented yet"; false
  | Cstruct _ -> print_debug "Found value of type struct"; false
  | _ -> print_debug "This shouldn't have happened"; raise CompileError

and compile_instr is_main = function
  (*
    Inputs:
      - Compiler Instructions
    Outputs:
      - x86 code corresponding to the given instruction.
  *)
  | Cnilinstr -> xorq !%rax !%rax
  | Cexpr e -> compile_expr e
  | Cblock es ->
    List.fold_left (fun code i -> code ++ compile_instr is_main i)
       (comment"compile new block") es
  | Cfor (ce, b) -> 
    let startforname = start_for_var_name !nb_for in
    let endforname = end_for_var_name !nb_for in
    nb_for := !nb_for + 1;
    jmp endforname ++
    label startforname ++
    compile_instr is_main b ++
    label endforname ++
    compile_expr ce ++
    movzbq !%al rax ++
    xorq !%rbx !%rbx ++
    cmpq !%rax !%rbx ++
    jne startforname
  | Cif (ce, b1, b2) -> 
    print_debug "Compiling Cif";
    let ifname = if_var_name !nb_ifelse in
    let elsename = else_var_name !nb_ifelse in
    nb_ifelse := !nb_ifelse + 1;
    print_debug "Compiling If condition";
    let condcmd = compile_expr ce in
    print_debug "Compiling If Block";
    let ifcmd = compile_instr is_main b1 in
    print_debug "Compiling Else Block";
    let elsecmd = compile_instr is_main b2 in
    print_debug "Done compiling Cif";
    condcmd ++
    movzbq !%al rax ++
    xorq !%rbx !%rbx ++
    cmpq !%rax !%rbx ++
    je elsename ++
    ifcmd ++ 
    jmp ifname ++
    label elsename ++
    elsecmd ++
    label ifname
  | CAssign_List (lce1, lce2) -> 
  begin
    let rhscmd = List.fold_left (
      fun cmd ce2 -> 
        print_debug "Comping r.h.s. expressions";
        comment"Compiling ce2" ++
        compile_expr ce2 ++
        comment"Compiled ce2" ++
        pushq !%rax ++ cmd
    ) nop lce2 in
    let lhscmd = 
    List.fold_left2 (fun cmd ce1 ce2 -> 
      print_debug "Compiling CAssign checking for nil";
      let bnil = is_nil ce2 in
      print_debug (sprintf "Found nil bool: %b" bnil);
      let lofs2 = find_lofs [] ce2 in
      List.iter ( fun ofs ->
      print_string (sprintf "%d, " ofs); ()) lofs2;
      print_string "\n";
      match ce1 with 
        | Cident (offset, id) -> 
            print_debug "Processing nil update - ident";
            let foo = match bnil with
              | true -> add_to_nil [offset] true (Hashtbl.find vars.vartypes id)
              | false -> add_to_nil [offset] true (Hashtbl.find vars.vartypes id);
                         Hashtbl.replace nil_info [offset] false
            in
            print_debug "Inheriting nil info";
            let rec check_prefix l1 l2 = 
              match l1, l2 with
               | l, [] -> (true, l) 
               | [], _ -> (false, [])
               | x::p, y::q when x = y -> check_prefix p q
               | _ -> (false, [])
            in 
            print_string (sprintf "Assigning to %s:ofs=%d" id offset);
            Hashtbl.iter (
              fun lofs b -> 
                let (is_prefix, suffix) = check_prefix lofs lofs2 in
                print_string (sprintf "Found: %b. For: " is_prefix);
                List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs;
                print_string " compared to: ";
                List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs2;
                print_string "\n";
                match is_prefix with
                | true -> 
                  print_string (sprintf "Adding nil info %b for: " b);
                  print_lofs ~isstring:true ([offset] @ suffix);
                  Hashtbl.replace nil_info ([offset] @ suffix) b;
                | false -> ()
            ) nil_info;
            (*Hashtbl.replace nil_info [offset] false;*)
            comment(sprintf "Assigning %s" id) ++
            popq rax ++ 
            movq !%rax (ind ~ofs:offset rbp) ++
            cmd
        | Cmethod (lsofs, aofs, strc, attr) -> 
            print_debug "Processing nil update - method";
            let cstruct = Hashtbl.find structs strc in
            let foo = match bnil with
              | true -> add_to_nil (lsofs @ [aofs]) true (Smap.find attr cstruct.fieldtypes)
              | false -> add_to_nil (lsofs @ [aofs]) true (Smap.find attr cstruct.fieldtypes); 
                         Hashtbl.replace nil_info (lsofs @ [aofs]) false
            in
            print_debug "Inheriting nil info";
            let rec check_prefix l1 l2 = 
              match l1, l2 with
               | l, [] -> (true, l) 
               | [], _ -> (false, [])
               | x::p, y::q when x = y -> check_prefix p q
               | _ -> (false, [])
            in 
            print_string (sprintf "Assigning to %s.%s" strc attr);
            Hashtbl.iter (
              fun lofs b -> 
                let (is_prefix, suffix) = check_prefix lofs lofs2 in
                print_string (sprintf "Found: %b. For: " is_prefix);
                List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs;
                print_string " compared to: ";
                List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs2;
                print_string "\n";
                match is_prefix with
                | true -> 
                  print_string (sprintf "Adding nil info %b for: " b);
                  print_lofs ~isstring:true ((lsofs @ [aofs]) @ suffix);
                  Hashtbl.replace nil_info ((lsofs @ [aofs]) @ suffix) b;
                | false -> ()
            ) nil_info;
            (*Hashtbl.replace nil_info (lsofs @ [aofs]) false;*)
            comment(sprintf "Assigning %s.%s" strc attr ) ++
            popq rax ++ 
            go_to_end_method lsofs r14 !%r14 ++
            movq !%rax (ind ~ofs:aofs r14) ++ 
            cmd
        | Cunop (Pointer, ce) -> 
              let t = type_ce ce1 in
              print_debug "Careful ! Nil assignment to left pointer is not done yet";
              print_debug (sprintf "lhs of type: %s" (type_to_string t));
              let out = comment"Assigning *ce" ++
              compile_expr ce ++
              popq r14 ++
              movq !%r14 (ind rax) ++
              cmd in print_debug "Done assigning pointer"; out
        | Cunop (op, ce) -> print_debug "Shouldn't happen!"; cmd
        | _ -> print_debug "This shouldnt happend"; cmd
    ) nop (lce1) (lce2)
    in
    rhscmd ++ lhscmd
  end
  | Cref (lid, lce, isreal) -> begin
      let rhscmd = List.fold_left(
        fun cmd ce2 -> 
          print_debug "Comping r.h.s. expressions";
          comment"Compiling ce2" ++
          compile_expr ce2 ++
          comment"Compiled ce2" ++
          pushq !%rax ++ cmd
      ) nop lce in
      let cmd = List.fold_left2 (fun cmd id ce -> 
        try
        begin
          let offset = Hashtbl.find vars.vartable id in
          print_debug (sprintf "Compiling Cref of %s" id);
          print_debug "Checking nil bool";
          let bnil = match isreal with
            | true -> is_nil ce 
            | false -> true
          in
          print_debug (sprintf "Found nil bool to be: %b" bnil);
          print_debug "Processing nil update - Cref";
          let foo = match bnil with
            | true -> add_to_nil [offset] true (Hashtbl.find vars.vartypes id)
            | false -> add_to_nil [offset] true (Hashtbl.find vars.vartypes id);
                        Hashtbl.replace nil_info [offset] false
          in
          print_debug "Done pre-processing nil update";
          let lofs2 = find_lofs [] ce in
          List.iter ( fun ofs ->
            print_string (sprintf "%d, " ofs); ()) lofs2;
          print_string "\n Gen Nil Info: \n";
          Hashtbl.iter (
            fun lofs b -> List.iter ( fun ofs ->
            print_string (sprintf "%d, " ofs); ()) lofs; print_string "\n"; ()
          ) nil_info;
          print_string (sprintf "Checking %s Cref\n" id);
          print_debug "Inheriting nil info";
          let rec check_prefix l1 l2 = 
            match l1, l2 with
              | l, [] -> (true, l) 
              | [], _ -> (false, [])
              | x::p, y::q -> if x = y then check_prefix p q else (false, [])
          in 
          Hashtbl.iter (
            fun lofs b -> 
              let (is_prefix, suffix) = check_prefix lofs lofs2 in
              print_string (sprintf "Found: %b. For: " is_prefix);
              List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs;
              print_string " compared to: ";
              List.iter (fun ofs -> print_string (sprintf "%d, " ofs) ) lofs2;
              print_string "\n";
              match is_prefix with
              | true -> 
                print_string "Adding nil info for:";
                print_lofs ~isstring:true ([offset] @ suffix);
                print_string "\n";
                Hashtbl.replace nil_info ([offset] @ suffix) b;
              | false -> ()
          ) nil_info;
          (* VEEEEEERY WEIRD :
          print_debug (sprintf "Finally value of nil bool is: %b" (Hashtbl.find nil_info [offset]));
          *)
          let target = Hashtbl.find vars.vartable id in
          let sink = (ind ~ofs:target rbp) in
          print_debug (sprintf "Putting adress into %s" id);
          comment(sprintf "Assigning %s" id) ++ 
          popq rax ++
          movq !%rax sink ++
          cmd
        end
        with Not_found -> print_debug (sprintf "Cref: Could not find target var %s" id); raise CompileError
      ) nop lid lce
      in print_debug "Done compiling Cref";
      rhscmd ++ cmd
  end
  | Cvar (lid, t, []) -> 
  begin
      comment"Assigning uninitialized vars" ++
      List.fold_left (fun cmd id -> 
        let target = Hashtbl.find vars.vartable id in
        let sink = (ind ~ofs:target rbp) in
        nop
    ) nop lid
  end
  | Creturn lce ->  comment"Displacing temporarily the return adress" ++
                    popq r13 ++
                    List.fold_left (fun cmd ce ->
                      cmd ++
                      comment"Pushing ret" ++
                      compile_expr ce ++
                      pushq !%rax 
                      ) nop lce ++ 
                    pushq !%r13 ++ ret
  | _ -> print_debug "hey 1"; nop


let compile_program env ofile =
  (*
    Main Compiler function.
      Inputs:
        - Typer Environment
        - Output File
      Outputs:
        Prints all the x86 code generated from
        compiling the Abstract Syntax Tree passed 
        from the typer into the out file.
  *)
  (* Allocating *)
  print_debug "Starting alloc \n";
  let alloced_env = alloc env in
  (* Done Allocating *)
  print_debug "2\n";
  (* Compiling *)
  let main_code, funct_code = 
    Smap.fold (fun fname body (cmain, cfuncs) ->
        (* Compiling is done function by function *)
        print_debug (sprintf "compiling %s\n" fname);
        if fname = "main"
        then comment"Compiling Main" ++ movq (ilab (Int.to_string ((!nb_vars+1) * 8))) !%rdi ++
               call "malloc" ++
               movq !%rax !% rbp ++ 
               compile_instr true body, cfuncs
        else 
        begin
          print_debug (sprintf "Detected non-main function %s" fname);
          print_debug "Looking for function info";
          let finfo = Hashtbl.find func_info fname in
          (* 
            If the function is not the main function
            we also have to take care of retreiving 
            the inputs that have been passed to it.
            Inputs are passed through the stack.
          *)
          print_debug "Found function info";
            cmain,
              comment"Compiling func" ++ cfuncs ++
                label fname ++
                comment"Temporarily Displacing return adress" ++
                popq r14 ++ 
                List.fold_left (fun cmd iid -> 
                                    let offset = Hashtbl.find vars.vartable iid in
                                    comment(sprintf "Retreiving var %s" iid) ++
                                    popq rax ++
                                    movq !%rax (ind ~ofs:offset rbp) ++
                                    cmd
                                ) nop finfo.input_ids ++
                comment"Moving return adress back to the stack" ++
                pushq !%r14 ++
                compile_instr false body ++
                ret
        end
        )
      alloced_env (nop, nop)
  in
  (* Done with compilation *)
  print_debug "3";

  (* Putting all together in a format that can
    be passed to x86_64.ml 
  *)
    let p =
    { text =
        globl "main" ++ label "main" ++
          main_code ++
          xorq !%rax !%rax ++ (* exit *)
          ret ++
          funct_code;
      data =
        Hashtbl.fold (fun s id l -> (label (string_var_name id))  ++ string s ++ l) string_decls 
        (label (string_var_name (0)) ++ string "\" \"")
    } in
  
  let f = open_out ofile in
  let fmt = formatter_of_out_channel f in
  X86_64.print_program fmt p;
  fprintf fmt "@?";
  close_out f
