open Go_ast
open Format
open Lexing
open Graph

exception Typing_error of string * (position * position)
exception The_end
exception Unfinished
exception Texprweird


module Smap = Map.Make(String)

let  raise_error emsg pos = raise (Typing_error (emsg, pos)) 
(* Environment *)
type tstruct = (typ Smap.t ) Smap.t (* struct name -> (var name -> type of var) *)
type tfunct = (gotype * gotype) Smap.t (* store name -> (args , return types), args = (types) *)
type tvars = (typ * bool ref * bool ref) Smap.t (* store name -> type of var , is_it_used_bool -> true if used else false *)
type typenv = { structs: tstruct; funct : tfunct; vars : tvars} 
(* Variable Set *)
module Vset = Set.Make(String)

(* Helper conversion of types functions *)

(* Compacts a list of gotype into a gotype *)

let rec gotypelist_to_typlist gtl curlist pos = match gtl with 
| [] -> curlist
| x :: l ->  match x with 
  | Tsimpl s -> gotypelist_to_typlist l (curlist @ [s]) pos
  | Tmany ls -> gotypelist_to_typlist l (curlist @ ls) pos

let gotypelist_to_gotype gtl pos = 
  let res = gotypelist_to_typlist gtl [] pos in
  match res with 
  | [] -> Tmany ([])
  | [x] -> Tsimpl x
  | _ as l -> Tmany l

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

(* TODO: name typegolist!!!! *)
(* Converts type_go -> typ list *)
let rec typego_to_typlist env tg = match tg with 
  | [] -> []
  | t :: lt -> (typego_to_typ env t) :: (typego_to_typlist env lt) 

(* Converts typ list to gotype  *)
let typlist_to_gotype tg = match tg with
  | [x] -> Tsimpl x
  | _ as l -> Tmany l

(* Converts gotype to typ list *)
let gotype_to_typlist gt = match gt with 
  | Tsimpl x -> [x]
  | Tmany l -> l

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

let varlist_to_typego vars =
  List.rev(List.fold_left (fun l (tuple, pos) -> let lids, typ = tuple in 
      List.fold_left (fun l2 _ -> typ :: l2) l lids
  ) [] vars)

let varlist_to_gotype env vars = typego_to_gotype env (varlist_to_typego vars)


let rec check_duplicate (mylist : ident loc list) = match mylist with
  | [] -> false
  | (id, pos) :: l when id <> "_" -> 
  if List.exists (fun (y,_) -> id = y) l
  then raise_error "RedundantVariable2" pos
  else check_duplicate l
  | (id,pos) :: l -> check_duplicate l

let rec check_duplicate_nopos_s mylist pos = match mylist with
  | [] -> false
  | id :: l when id <> "_" -> 
  if List.exists (fun y -> id = y) l
  then raise_error "RedundantVariable heya" pos
  else check_duplicate_nopos_s l pos
  | id :: l -> check_duplicate_nopos_s l pos

let rec check_duplicate_nopos mylist pos = match mylist with
  | [] -> false
  | id :: l when id <> "_" -> 
  if List.exists (fun y -> id = y) l
  then raise_error "RedundantVariable3" pos
  else check_duplicate_nopos l pos
  | id :: l -> check_duplicate_nopos l pos

let rec check_underscore lexp =
  match lexp with 
  | [] -> ()
  | ((Eident "_"), pos) :: l -> raise_error "underscore return" pos
  | (_,_):: l -> check_underscore l 

let rec compare_gotypes exprtypes inputstypes givenexpr pos = match exprtypes, inputstypes, givenexpr with
  |  Tsimpl (Tstar Tnone), Tsimpl (Tstar _ ), [] -> true
  |  Tsimpl (Tstar Tnone), Tsimpl (Tstar _ ), [(Econst ENil, _)] -> true
  |  Tsimpl a, Tsimpl b, _ when a = b -> true
  |  Tmany([]), Tmany(a::x), _ -> raise_error "function takes more arguments" pos
  |  Tmany(a::x), Tmany([]), _ -> raise_error "function takes less arguments" pos
  |  Tmany( []), Tmany([]), _ -> true 
  |  Tmany ((Tstar Tnone) :: x), Tmany ((Tstar s) :: y), e::l when fst e = Econst ENil -> compare_gotypes (Tmany x) (Tmany y) l pos
  |  Tmany (a :: x), Tmany (b :: y), e::l when (a = b) -> compare_gotypes (Tmany x) (Tmany y) l pos
  |  Tmany (a :: x), Tmany (b :: y), [] when (a = b) -> compare_gotypes (Tmany x) (Tmany y) [] pos
  |  _,_,_ -> false

(* TODO: change name compare_typlist_with_typ *)
let rec compare lt t =  match lt with 
  | [] -> true
  | a :: l -> if (a = t) || (a = Tstar Tnone) then compare l t else false

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
          try let (ts,used, shadow) = Smap.find name env.vars in 
              used := true;
              (Tsimpl ts, Eident name, pos, true)
          with Not_found -> 
            if Smap.mem name env.structs then
              (Tsimpl(Tstruct name), Eident name, pos, true)
            else  raise_error "Notfound_ident" pos
      end
      |Eident "_" -> (Tsimpl Tvoid, Eident "_", pos, false) (* TODO check bool*)
      |Eident _ -> raise The_end 
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
              | (Tsimpl ta, _,_,false) -> raise_error "Leftvalue 2" pos 
              | (Tmany _,_,_,_) -> raise_error "Tsimplrequired" pos
            end 
          | Pointer -> begin
            if t = Tsimpl Tnone then raise_error "PointerMissing" pos
            (*else if b1 = true then raise_error "Leftvalue 3" pos *)
            else if e = Econst ENil then raise_error "Cant assign Nil idiot" pos
            else begin match t with
                 | Tsimpl Tstar ta -> (Tsimpl ta , Eunop(Pointer, (e,p)), pos, true)
                 | _ -> raise_error "Invalidargument 1" pos end 
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
        (* TODO: Check Nil case *)
        | _ -> raise_error "Expectedstructgot 60" pos
      end 
      | Eprint le -> begin 
            let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
            (Tsimpl Tnone, Eprint exprs, pos, false)
            end
      | Enew le -> begin 
          if List.length le = 0 then raise_error "new() takes an argument you have given none" pos
          else if List.length le > 1 then raise_error "new() takes only one argument" pos
          else let e = List.hd le in (* CHECK IF NEED TO CALL TYPE_EXPR E *)
            match fst e with 
            | Eident s -> if Smap.mem s env.structs 
            then let t, exp, p, b = type_expr env e in
              (Tsimpl (Tstar (Tstruct s)) , Eunop(Pointer, (exp,p)), pos, false) (* BOOL should be false! *)
            else raise_error "struck unknown name" pos
            | _ -> raise_error "new() takes as argument a struct type only" pos 
            end
      | Ecall (id, le)->  begin
          try begin
              let tinputs, tout = Smap.find id env.funct in
              let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
              if not(compare_gotypes (gotypelist_to_gotype types pos) tinputs exprs pos) then 
              raise_error "Not the same types" pos
              else (tout, Ecall (id, exprs), pos, false) end 
            with Not_found -> raise_error "Notfound_funct" pos end 

(* Type Instructions: 'a -> 'b -> 'c -> 'a * 'd * bool * bool   *)
(* returns (env, tree, ret_bool, print_bool) 
  where if there is a return ret_bool = true and if there is a print print_bool =true *)

(*and recall_funct env le =
    let t, expr, b  = help_unwrap (List.map (type_expr env) le) in
        match exprs with 
        | Ecall (id, e) -> recall_funct env e 
        | _ -> (t, expr, b)*)

and type_instruction env trets = function (* Error: the tree :/ *)
  | [] -> env, [], false, false
  | (Iblock(b, pos_b), pos_instr) :: block ->
      let shadowed_vars = Smap.fold (fun id (a, b, c) nm -> Smap.add id (a, b, ref true) nm) env.vars Smap.empty in
      let shadowed_env = {env with vars = shadowed_vars} in
      let tmpenv, tree1, rb1, pb1 = type_instruction shadowed_env trets b in
      (* updates the used bool of real env from tmpenv *)
      let new_vars = Smap.fold (fun id (a, b, c) nm -> let (_, used_in_block, _) = Smap.find id tmpenv.vars in
      Smap.add id (a, ref (!used_in_block || !b), c) nm) env.vars Smap.empty in
      let new_env = {env with vars = new_vars} in
      (* call on new_env *)
      let env, tree2, rb2, pb2 = type_instruction new_env trets block in
      env,(Iblock(tree2, pos_b), pos_instr) :: tree1, rb1 || rb2, pb1 || pb2
  | (Iif (instr_if, pos_if), pos_instr) :: block -> begin
      let e_pos, (b1, pos_b1), (b2, pos_b2) = instr_if in 
      let typ, expr, pos_expr, left = type_expr env e_pos in 
      let env , tree1, rb1, pb1 = type_instruction env trets b1 in
      let env , tree2, rb2, pb2 = type_instruction env trets b2 in
      let env , tree3, rb3, pb3 = type_instruction env trets block in
      match typ with 
      | Tsimpl Tbool -> env, (Iif(instr_if, pos_if),pos_instr)::tree3 , ((rb1 && rb2) || rb3), pb1 || pb2 || pb3
      | Tmany _ | Tsimpl _ -> raise_error "Expected bool bla" pos_instr
     
  end
  | (Ifor (e_pos, b_pos), pos_instr)::block -> begin 
      let typ, expr, pos_expr, left = type_expr env e_pos in
      let env1, tree1, rb1, pb1 = type_instruction env trets (fst b_pos) in
      let env2, tree2, rb2, pb2 = type_instruction env trets block in 
      match typ with 
      | Tsimpl Tbool -> env, (Ifor (e_pos, b_pos),pos_instr)::tree2, rb2 , pb1 || pb2 (* TODO: check *)
      | Tsimpl _ | Tmany _ -> raise_error "Expected bool " (snd(e_pos)) 
  end 
  | (Ireturn (le_pos), pos_instr):: block -> begin
    let types, exprs, _  = help_unwrap (List.map (type_expr env) le_pos) in 
    check_underscore exprs;
    (* return empty *)
    if compare_gotypes (gotypelist_to_gotype types pos_instr) (typeret_to_gotype env trets) exprs pos_instr then begin
      let env , tree, rb, pb = type_instruction env trets block in
      env, (Ireturn(exprs),pos_instr)::tree , true, pb end
    else raise_error "Not the same types" pos_instr
  end 
  | (Ivar ( lid, tygo_pos, le_pos), pos_instr)::block -> 
    check_duplicate_nopos lid pos_instr;
    let types, exprs, lb  = help_unwrap (List.map (type_expr env) le_pos) in 
    let typlist_types = gotype_to_typlist (gotypelist_to_gotype types pos_instr) in 
    let ty = typego_to_typ env tygo_pos in 
    let return_helper lid ty = 
      let newvars = List.fold_left( fun m id -> 
        if Smap.mem id m && id <> "_" then raise_error "Redundant variable 4" pos_instr 
        else Smap.add id (ty, ref false, ref false) m ) env.vars lid in 
      let newenv = {env with vars = newvars} in 
      let env, tree, rb, pb = type_instruction newenv trets block in
      env, (Ivar (lid, tygo_pos, exprs), pos_instr)::tree, rb, pb 
    in begin
    match ty with 
      | Tnone -> (let tmptyp = List.hd typlist_types in
        if not(compare typlist_types tmptyp) 
        then raise_error "Not the same types (Ivar)" pos_instr
      else return_helper lid tmptyp)
      | _ -> ( if not(compare typlist_types ty) 
            then raise_error "Not the same types (Ivar)" pos_instr
            else return_helper lid ty)
      end
  | (Inil, pos_instr)::block -> type_instruction env trets block 
  | (Iinstrsimpl((Isexpr( Eprint(le_pos), pos_print)), pos_isexpr) , pos_instr)::block -> 
    let types, exprs, _  = help_unwrap (List.map (type_expr env) le_pos) in 
    let env, tree, rb, pb = type_instruction env trets block in 
    env, (Iinstrsimpl((Isexpr( Eprint(exprs), pos_print)), pos_isexpr) , pos_instr)::tree, rb, true
  | (Iinstrsimpl((Isexpr (Ecall(id, le),pos)), pos_isexpr),pos_instr)::block -> 
    let typ, expr, expr_pos, _  = type_expr env (Ecall(id, le),pos) in
    let (_, tout) = Smap.find id env.funct in
    let is_func_returning = (List.length (gotype_to_typlist tout) > 0) in
    let env, tree, rb, pb = type_instruction env trets block in 
    env, (Iinstrsimpl((Isexpr (expr,expr_pos)), pos_isexpr),pos_instr)::tree, is_func_returning && rb, pb
  | (Iinstrsimpl((Isexpr  e_pos), pos_isexpr),pos_instr)::block -> 
    let typ, expr, expr_pos, _  = type_expr env e_pos in 
    let env, tree, rb, pb = type_instruction env trets block in 
    env, (Iinstrsimpl((Isexpr (expr,expr_pos)), pos_isexpr),pos_instr)::tree, rb, pb
  | (Iinstrsimpl((Isassign_incdec (e1_pos, e2_pos)), pos_asgn),pos_instr)::block -> 
    let typ1, expr1, expr_pos1, _  = type_expr env e1_pos in 
    let typ2, expr2, expr_pos2, _  = type_expr env e2_pos in 
    let env, tree, rb, pb = type_instruction env trets block in
    if typ1 <> Tsimpl Tint then raise_error "Expected int for incr or decr" pos_instr
    else begin 
      let e1 , e2 = (expr1, expr_pos1),( expr2, expr_pos2)in  
      env, (Iinstrsimpl((Isassign_incdec (e1,e2)), pos_asgn),pos_instr)::tree, rb, pb 
    end 
  | (Iinstrsimpl((Isassign_list (le1_pos, le2_pos)), pos_lasgn),pos_instr)::block -> 
    let types1, exprs1, b1  = help_unwrap (List.map (type_expr env) le1_pos) in 
    let types2, exprs2, b2  = help_unwrap (List.map (type_expr env) le2_pos) in 
    (* TODO: ADDED to fix typing/bad/leftvalue - unsure if its correct *)
    if List.exists (fun b -> b = false) b1 then raise_error "Leftvalue 1" pos_instr else begin  
    if compare_gotypes (gotypelist_to_gotype types2 pos_lasgn) (gotypelist_to_gotype types1 pos_lasgn) exprs2 pos_instr then 
      begin 
        let env, tree, rb, pb = type_instruction env trets block in 
        env, (Iinstrsimpl((Isassign_list (exprs1, exprs2)), pos_lasgn),pos_instr)::tree, rb, pb
      end
    else raise_error "Not equal types for the two expressions" pos_instr end 
  | (Iinstrsimpl((Isref (lid, le_pos)), pos_ref),pos_instr)::block ->
    check_duplicate_nopos lid pos_instr;
    let types, exprs, lb  = help_unwrap (List.map (type_expr env) le_pos) in 
    let typlist_types = gotype_to_typlist (gotypelist_to_gotype types pos_instr) in 
    let return_helper lid ty = 
      let newvars = List.fold_left( fun m id -> 
      if Smap.mem id m && id <> "_" then let (_, _, shadow) = Smap.find id m in
      if not(!shadow) then raise_error "Redundant variable 5" pos_instr 
      else Smap.add id (ty, ref true, ref false) m (* Shadowing previous var *)
      else Smap.add id (ty, ref false, ref false) m ) env.vars lid in  (* Var does not exist yet *)
      let newenv = {env with vars = newvars} in 
      let env, tree, rb, pb = type_instruction newenv trets block in
      env, (Ivar (lid, (Nonetype_go,pos_ref), exprs), pos_instr)::tree, rb, pb 
    in
    let tmptyp = List.hd typlist_types in
    if not(compare typlist_types tmptyp) then raise_error "Not the same types (Ivar)" pos_instr
    else return_helper lid tmptyp
    (*type_instruction env trets ((Ivar (lid, (Nonetype_go,pos_instr), le_pos), pos_instr)::block)*)

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
        (* TODO: check if function takes these many arguments or returns *)
        let arg_types = varlist_to_gotype env vars in 
        let ret_types = typeret_to_gotype env trets in 

        {structs = env.structs; funct = Smap.add id (arg_types, ret_types) env.funct; vars = env.vars}
      end
      else
        raise_error "huh?" pos    
    end

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

let check_recursive_struct env = 
  let pos = (Lexing.dummy_pos , Lexing.dummy_pos) in 
  let g = mk_graph() in 
  Smap.iter (fun s _ -> add_node g s) env.structs;
  Smap.iter (fun s_id map -> 
    Smap.iter ( fun id typs -> 
      match typs with 
      | Tstruct st -> begin
          try Smap.find st env.structs;
          add_edge g s_id st
          with Not_found -> () end 
      | _ -> ()
      ) map
    ) env.structs;
  if has_cycle g then raise_error "Recursive struct" pos (* TODO: save positions for structs? *)
  else ()


(* Check if the function is well-typed  *)
let type_function env (f,pos) = 
  let dpos = Lexing.dummy_pos , Lexing.dummy_pos in 
  let id, vars, (trets, tpos), block_pos = f in
  let (tin, tout) = Smap.find id env.funct in
  let newvars = List.fold_left (fun s (((ids, t), pos) : Go_ast.vars loc) ->
          let tau = typego_to_typ env t in 
          List.fold_left (fun s id -> Smap.add id (tau,ref false, ref true) s) s ids) Smap.empty vars in
  let env, tree, rb, pb = type_instruction {env with vars = newvars} trets (fst(block_pos)) in 
  (* check cases of trets and return bool *)
  (* TODO: return the right position for the variables ! *)
  Smap.iter (fun id (t, used, shadow) -> if not(!used) && (id <> "_") then raise_error "unused variable" dpos) env.vars;
  match tout, rb with 
  | (Tmany []), true -> raise_error "No return expected" tpos
  | (Tmany (a::l)) , false -> raise_error "Expected return" tpos
  | Tsimpl a , false -> raise_error "Expected return " tpos
  | _, _ -> env , tree, rb, pb 

let type_main_function env = 
  (* always have package main otherwise parsing error *)
  let pos = (Lexing.dummy_pos, Lexing.dummy_pos) in 
  try match Smap.find "main" env.funct with 
      | Tmany [], Tmany [] -> ()
      | _,Tmany [] -> raise_error "Main can't have arguments" pos
      | Tmany [], _ -> raise_error "Main can't have return types" pos
      | _,_ -> raise_error "Main can't have arguments and return types" pos 
  with Not_found -> raise_error "Missing main" pos

(* Combine all functions *)

let type_prog program =
  let prog, fmtpackage = program in
  let pos = (Lexing.dummy_pos, Lexing.dummy_pos) in
  let env = { structs= Smap.empty; funct = Smap.empty ; vars = Smap.empty }  in
  let env = List.fold_left add_struct_to_env env prog in
  let env = List.fold_left add_vars_to_struct env prog in 
  check_recursive_struct env;
  let env = List.fold_left add_function_to_env env prog in
  type_main_function env;
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
  match printbool, fmtpackage with 
  | false, true -> raise_error "Unused import package" pos
  | true, false -> raise_error "You have not imported the fmt package" pos
  | _, _ -> env, function_tree

(* TODO: check that a call of a function is done correctly i.e number of inputs 
  TODO: why cant i do shadowing *)