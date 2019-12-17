open Go_ast
open Format
open Lexing

exception Typing_error of string * (position * position)
exception The_end
exception Unfinished
exception Texprweird


module Smap = Map.Make(String)

let  raise_error emsg pos = raise (Typing_error (emsg, pos)) 
(* Environment *)
type tstruct = (typ Smap.t ) Smap.t
type tfunct = (gotype * gotype) Smap.t (* store name -> (args , return types), args = (types) *)
type tvars = typ Smap.t 
type typenv = { structs: tstruct; funct : tfunct; vars : tvars } 
(* Variable Set *)
module Vset = Set.Make(String)

(* Helper conversion of types functions *)

(* Compacts a list of gotype into a gotype *)
(* TODO: CHECK ERRORS HERE!! *)
let rec gotypelist_to_gotype gtl curList pos = match gtl with
  | [] -> begin
    match curList with
    | [x] -> Tsimpl x
    | x::y::ls as c -> Tmany c
    | _ -> raise_error "weird gotype" pos 
    end
  | gt::gl -> begin match gt with 
    | Tsimpl s -> gotypelist_to_gotype gl (curList @ [s]) pos 
    | Tmany s -> gotypelist_to_gotype gl (curList @ s) pos 
    | _ -> raise_error "weird gotype 2" pos end
  | _ -> raise_error "weird gotype 3" pos 

(* Converts parser type to typer type : type_go -> typ  *)
let rec typego_to_typ env tg = 
  let t, pos = tg in  
  match t with
    | Tident "int" -> Tint
    | Tident "string" -> Tstring
    | Tident "bool" -> Tbool
    | Tident s -> if Smap.mem s env.structs then Tstruct s
                  else raise_error "Notfound_struct1" pos
    | Tmult p -> Tstar (typego_to_typ env p)
    | Nonetype_go -> Tnone

(* Converts type_go -> typ list *)
let rec typego_to_typlist env tg = match tg with 
  | [] -> []
  | t :: lt -> (typego_to_typ env t) :: (typego_to_typlist env lt) 

(* Converts typ list to gotype  *)
let typlist_to_gotype tg = match tg with
  | [x] -> Tsimpl x
  | _ as l -> Tmany l

(* Converts parser type to typer type: type_go -> gotype *)
let typego_to_gotype env tg = typlist_to_gotype (typego_to_typlist env tg)

(* Converts parser type to typer type: type_retour -> gotype *)
let typeret_to_gotype env tr = match tr with 
  | Tretour tg -> typego_to_gotype env [tg]
  | Tretour_list lg -> typego_to_gotype env lg
  | Nonetype_ret -> typego_to_gotype env []
 
(* Other functions *)
let varlist_to_id_and_typego env (lst:Go_ast.vars list) =
  List.fold_left (fun typs (ids, typ) -> typego_to_typ env typ :: typs) [] lst
let varlist_to_ids vars = begin
  let x = List.split(fst (List.split vars)) in
  List.flatten (fst x)
  end
let varlist_to_typego vars = begin
  let x = List.split(fst (List.split vars)) in
  snd x
  end
let varlist_to_gotype env vars = typego_to_gotype env (varlist_to_typego vars)


let rec check_duplicate (mylist : ident loc list) = match mylist with
  | [] -> false
  | (id, pos) :: l -> 
  if List.exists (fun (y,_) -> id = y) l
  then raise_error "RedundantVariable" pos
  else check_duplicate l

let rec check_underscore lexp =
  match lexp with 
  | [] -> false
  | ((Eident "_"), pos) :: l -> raise_error "underscore return" pos
  | (_,_):: l -> check_underscore l 

let rec compare t1 t2 pos = match t1, t2 with 
  |  Tsimpl a, Tsimpl b when a = b -> true
  |  Tmany (a :: x), Tmany (b :: y) when a = b ->  compare (Tmany x) (Tmany y) pos
  | _,_ -> raise_error "not the same type" pos

let rec help_unwrap = function 
    |[] -> [],[],[]
    |(a,b,c,d)::l2 ->  let la,lb,lc = help_unwrap l2 in 
    a::la,(b,c)::lb,d::lc


(* Type Expressions : typenv -> 'a * 'b -> gotype * 'c * 'b * bool *)
(* Return (typ, expr, position_expr, bool)  where if bool = true then we have a left value *)
let rec type_expr env le_pos = 
    let te, pos = le_pos in 
    match te with
      |Econst c -> begin match c with
          |Eint64 i -> (Tsimpl Tint, Econst (Eint64 i), pos, false)
          |Ebool  b -> (Tsimpl Tbool, Econst (Ebool b), pos, false)
          |Estring s -> (Tsimpl Tstring, Econst (Estring s), pos, false)
          |ENil -> (Tsimpl (Tstar Tnone), Econst (ENil), pos, false)
      end
      |Eident name when name <> "_"-> begin 
          try let ts = Smap.find name env.vars in 
              (Tsimpl ts, Eident name, pos, true)
          with Not_found -> raise_error "Notfound_ident" pos
      end
      |Eident "_" -> (Tsimpl Tvoid, Eident "_", pos, false)
      |Eident _ -> assert false
      |Eunop (unop, te) -> begin 
        let t,e,p,b1 = type_expr env te in
        match unop with 
          | Not -> begin
            if t <> Tsimpl Tbool then raise_error "Expectedboolgot" pos
            else (Tsimpl Tbool, Eunop(Not, (e,p)), pos, false) end
          | Sign -> begin 
            if t <> Tsimpl Tint then raise_error "Expectedintgot" pos
            else (Tsimpl Tint, Eunop(Sign, (e,p)), pos, false) end
          | Address -> begin match (t,e,p,b1) with
              | (Tsimpl ta, expr, _, true) -> (Tsimpl (Tstar ta), Eunop(Address, (e,p)), pos, false)
              | (Tsimpl ta, _,_,_) ->raise_error "Leftvalue" pos 
              | (Tmany _,_,_,_) -> raise_error "Tsimplrequired" pos
            end 
          | Pointer -> begin
            if t = Tsimpl Tnone then raise_error "PointerMissing" pos
            else if b1 = true then raise_error "Leftvalue" pos 
            else begin match t with
                 | Tsimpl Tstar ta -> (Tsimpl ta , Eunop(Pointer, (e,p)), pos, true)
                 | _ as c -> raise_error "Invalidargument" pos end 
            end
        end
      |Ebinop(binop, e1, e2) -> begin
        let t1,exp1, p1,b1 = type_expr env e1 in 
        let t2,exp2, p2,b2 = type_expr env e2 in
        match binop with
          | And | Or -> begin match t1, t2 with 
            | Tsimpl Tbool, Tsimpl Tbool -> Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos,false
            | _, Tsimpl Tbool -> raise_error "Expectedboolgot" p1
            | _, _ -> raise_error "Expectedboolgot" p2 end
          | Add| Minus| Mult| Div|Mod -> begin match t1, t2 with 
            | Tsimpl Tint, Tsimpl Tint -> Tsimpl Tint, Ebinop(binop, (exp1,p1), (exp2,p2)),pos,false
            | _, Tsimpl Tint -> raise_error "Expectedintgot" p1
            | _, _ -> raise_error "Expectedintgot" p2 end
          | Lt | Leq |Gt|Geq -> begin match t1, t2 with 
            | Tsimpl Tint, Tsimpl Tint -> Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false
            | _, Tsimpl Tint -> raise_error "Expectedintgot" p1
            | _, _ -> raise_error "Expectedboolgot" p2 end
          | Iseq | Neq -> begin match t1, t2 with 
            | Tsimpl (Tstar Tnone), Tsimpl (Tstar Tnone) -> raise_error "CantCompareNil" pos 
            | Tsimpl (Tstar Tnone), Tsimpl (Tstar _) | Tsimpl (Tstar _), Tsimpl (Tstar Tnone)-> 
                (Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false) 
            | t1, t2 when t1 = t2 -> (Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false) 
            | _,_ -> raise_error "UnequalTypes" pos end
      end 
      | Emethod(e, id) -> begin match type_expr env e with 
        | (Tsimpl (Tstruct s), expr, p, left) 
        | (Tsimpl (Tstar (Tstruct s)), expr, p, left) -> 
        begin 
          try let ts = Smap.find s env.structs in 
            try let tid = Smap.find id ts in 
                (Tsimpl tid, Emethod((expr,p), id), pos, left)
            with Not_found -> raise_error "Notfound_ident" pos
          with Not_found -> raise_error "Notfound_struct2" pos  
        end 
        | (t,_,_,_) -> raise_error "Expectedstructgot t" pos
      end 
      | Eprint le -> begin 
            let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
            (Tsimpl Tnone, Eprint exprs, pos, false)
            end
      | Ecall (id, le) ->  try begin
            let tinputs, tout = Smap.find id env.funct in
            let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
            match tinputs, gotypelist_to_gotype types [] pos with
            | t1, t2 when t1 = t2 -> (tout, Ecall (id, exprs), pos, false)
            | _ as c1, c2 -> raise_error "Invalidargument" pos
          end
          with Not_found -> raise_error "Notfound_funct" pos 
      | _ -> raise (Texprweird)

(* Type Instructions: 'a -> 'b -> 'c -> 'a * 'd * bool * bool   *)
(* returns (env, tree, ret_bool, print_bool) 
  where if there is a return ret_bool = true and if there is a print print_bool =true *)


and type_instruction env trets = function (* Error: the tree :/ *)
  | [] -> env, [], false, false
  | (Iblock(b, pos_b), pos_instr) :: block -> 
      let env, tree1, rb1, pb1 = type_instruction env trets b in
      let env, tree2, rb2, pb2 = type_instruction env trets block in
      env,(Iblock(tree2, pos_b), pos_instr) :: tree1, rb1 && rb2, pb1 || pb2
  | (Iif (instr_if, pos_if), pos_instr) :: block -> begin
      let e_pos, (b1, pos_b1), (b2, pos_b2) = instr_if in 
      let typ, expr, pos_expr, left = type_expr env e_pos in 
      let env , tree1, rb1, pb1 = type_instruction env trets b1 in
      let env , tree2, rb2, pb2 = type_instruction env trets b2 in
      let env , tree3, rb3, pb3 = type_instruction env trets block in
      match typ with 
      | Tsimpl _ | Tmany _ -> raise_error "Expected bool " pos_instr
      | Tsimpl Tbool -> env, (Iif(instr_if, pos_if),pos_instr)::tree3 , rb1 && rb2, pb1 || pb2 
  end
  | (Ifor (e_pos, b_pos), pos_instr)::block -> begin 
      let typ, expr, pos_expr, left = type_expr env e_pos in
      let env1, tree1, rb1, pb1 = type_instruction env trets (fst b_pos) in
      let env2, tree2, rb2, pb2 = type_instruction env trets block in 
      match typ with 
      | Tsimpl _ | Tmany _ -> raise_error "Expected bool " (snd(e_pos))
      | Tsimpl Tbool -> env, (Ifor (e_pos, b_pos),pos_instr)::tree2, rb1, pb1 
  end 
  | (Ireturn (le_pos), pos_instr):: block -> begin
    let types, exprs, _  = help_unwrap (List.map (type_expr env) le_pos) in 
    let foo = check_underscore exprs in 
    if (gotypelist_to_gotype types [] pos_instr) = (typeret_to_gotype env trets) then begin
      let env , tree, rb, pb = type_instruction env trets block in
      env, (Ireturn(exprs),pos_instr)::tree , true, pb end
    else raise_error "Not the same types" pos_instr
  end (*
  | (Ivar ( lid, tygo_pos, le_pos), pos_instr)::block -> 
    let types, exprs, _  = help_unwrap (List.map (type_expr env) le_pos) in 
    let newvars = List.fold_left (fun s (((ids, t), pos)) ->
          let tau = typego_to_typ env t in 
          List.fold_left (fun s id -> Smap.add id tau s) s ids) Smap.empty env.vars in
    let newenv = { env with vars = newvars} in 
    let env , tree, rb, pb = type_instruction newenv trets block in
  *)
  | (Iinstrsimpl((Isexpr  e_pos), pos_isexpr),pos_instr)::block -> assert false
  | (Iinstrsimpl((Isassign_incdec (e1_pos, e2_pos)), pos_asgn),pos_instr)::block -> assert false
  | (Iinstrsimpl((Isassign_list (le1_pos, le2_pos)), pos_lasgn),pos_instr)::block -> assert false
  | (Iinstrsimpl((Isref (lid, le_pos)), pos_ref),pos_instr)::block -> assert false
  | _ -> raise (Unfinished)


(* Add functions and check their unicity *)
let add_function_to_env env d = match d with
  | Dstruct _ -> env
  | Dfunc ((id, vars, (trets, tpos), b),pos) ->
    if Smap.mem id env.funct then raise_error "RedundantFunctionName" pos
    else 
    begin
      let ids_gtpos = List.fold_left (fun vs var -> 
        let (ids, _), pos = var in 
        (List.map (fun id -> (id, pos)) ids) @ vs)
        [] vars in
      if not( check_duplicate ids_gtpos ) then 
      begin
        let arg_types = varlist_to_gotype env vars in 
        let ret_types = typeret_to_gotype env trets in 
        {structs = env.structs; funct = Smap.add id (arg_types, ret_types) env.funct; vars = env.vars}
      end
      else
        raise_error "huh?" pos    
    end

let rec check_duplicate (mylist : ident loc list) = match mylist with
  | [] -> false
  | (id, pos) :: l -> 
  if List.exists (fun (y,_) -> id = y) l
  then raise_error "RedundantVariable" pos
  else check_duplicate l

(* Add structures and check their unicity *)
let add_struct_to_env env d = match d with
  | Dfunc _ -> env
  | Dstruct ((id, vars),pos) -> 
    if Smap.mem id env.structs then raise_error "RedundantStructName" pos
    else {env with structs = Smap.add id Smap.empty env.structs }

let add_vars_to_struct env d = match d with
  | Dfunc _ -> env
  | Dstruct ((id, vars),pos) -> 
      let ids_gtpos = List.fold_left (fun vs var -> 
        let (ids, _), pos = var in 
        (List.map (fun id -> (id, pos)) ids) @ vs)
        [] vars in
      if not( check_duplicate ids_gtpos ) then 
      begin
        let newStruct = List.fold_left (fun s (((ids, t), pos) : Go_ast.vars loc) ->
          let tau = typego_to_typ env t in 
          List.fold_left (fun s id -> Smap.add id tau s) s ids) Smap.empty vars in
        { env with structs = Smap.add id newStruct env.structs }
      end
      else
        raise_error "buh?" pos


(* Check if the function is well-typed  *)
let type_function env (f,pos) = 
  let id, vars, (trets, tpos), block_pos = f in
  let (tin, tout) = Smap.find id env.funct in
  let newmax = List.fold_left (fun s (((ids, t), pos) : Go_ast.vars loc) ->
          let tau = typego_to_typ env t in 
          List.fold_left (fun s id -> Smap.add id tau s) s ids) Smap.empty vars in
  let env, tree, rb, pb = type_instruction {env with vars = newmax} trets (fst(block_pos)) in 
  (* check cases of trets and return bool *)
  match tout, rb with 
  | (Tmany []), true -> raise_error "No return expected" tpos
  | (Tmany (a::l)) , false -> raise_error "Expected return" tpos
  | Tsimpl a , false -> raise_error "Expected return " tpos
  | _, _ -> env , tree, rb, pb   

(* Combine all functions *)

let type_prog prog = 
  let env = { structs= Smap.empty; funct = Smap.empty ; vars = Smap.empty }  in
  let env = List.fold_left add_struct_to_env env prog in
  let env = List.fold_left add_vars_to_struct env prog in 
  let env = List.fold_left add_function_to_env env prog in
  (* check_recursive_struct *)
  let rec read_function printing = function 
    | [] -> printing, []
    | (Dstruct s)::l -> read_function printing l 
    | (Dfunc f)::l -> begin 
        let env, tree_pos, rb, pb = type_function env f in
        let printbool , newtree = read_function (printing || pb) l in
        (printbool, tree_pos::newtree) (* error here maybe *)
      end 
  in
  let printbool, function_tree = read_function false prog in 
  (* need to check for import fmt *)
  env, function_tree
