open Go_ast
open Format

exception Typing_error


module Smap = Map.Make(String)

(*Type types*)
type typ = 
    | Tint
    | Tbool
    | Tstring
    | Tstruct of string
    | Tstar of typ
    | Tnone
    | Tvoid
    (*Functions hold their argument types, return types, and environment in which they were defined 
    | Typfunc of ttyp list * ttyp * ttyp StringMap.t *)

type gotype = 
    | Tsimpl of typ 
    | Tmany of typ list 

type ems =  | Notfound_ident of string | Notfound_struct of string | Notfound_funct of string
            | Expectedboolgot of gotype | Expectedintgot of gotype | Expectedstructgot of gotype | Expectedstringgot of gotype
            | Unknownstruct of string | Invalidargument | CantCompareNil | RedundantVariable | RedundantFunctionName of string
            | Leftvalue | Wrongtype | Printing | Tsimplrequired | PointerMissing | RedundantStructName | InvalidReturns
            | UnequalTypes of gotype * gotype  | RedundantField | Jailaflemme | FunctionReturnTypesDoNotCorrespond

let raise_error emsg pos = raise Typing_error
type tstruct = (typ Smap.t ) Smap.t
type tfunct = (gotype * gotype) Smap.t (* store name -> (args , return types), args = (types) *)
type tvars = typ Smap.t 
(*Store the types in env*)
type typenv = { structs: tstruct; funct : tfunct; vars : tvars } 


let rec gotypelist_to_gotype gtl curList = match gtl with
  | [] -> begin
    match curList with
    | [x] -> Tsimpl x
    | x::y::ls as c -> Tmany c
    | _ -> raise Typing_error
    end
  | gt::gl -> begin match gt with 
    | Tsimpl s -> gotypelist_to_gotype gl (curList @ [s])
    | Tmany s -> gotypelist_to_gotype gl (curList @ s)
    | _ -> raise Typing_error end
  | _ -> raise Typing_error


(*print function*)
let rec p_type oc t =
    match t with    
        |Tint -> Printf.fprintf oc "int";
        |Tbool -> Printf.fprintf oc "bool";
        |Tstring -> Printf.fprintf oc "string";
        |Tstruct s -> Printf.fprintf oc "%s" s;
        |Tstar t -> Printf.fprintf oc "*"; p_type oc t (* "*%a" p.. *)
        |Tnone -> Printf.fprintf oc "none"
        |Tvoid -> Printf.fprintf oc "void"

(* Part 2.a checking correctness of function delcaration*)

module Vset = Set.Make(String)
(*module Vset = Set.Make(struct type t = ident let compare = compare end)*)

let rec typego_to_typ env tg = let t, pos = tg in  match t with
  | Tident "int" -> Tint
  | Tident "string" -> Tstring
  | Tident "bool" -> Tbool
  | Tident s -> if Smap.mem s env.structs then Tstruct s else raise_error (Unknownstruct s) pos
  | Tmult p -> Tstar (typego_to_typ env p)
  | Nonetype_go -> Tnone

let rec typego_to_typlist env tg = match tg with 
  | [] -> []
  | t :: lt -> (typego_to_typ env t) :: (typego_to_typlist env lt) 

let typlist_to_gotype tg = match tg with
  | [x] -> Tsimpl x
  | _ as l -> Tmany l

let typego_to_gotype env tg = typlist_to_gotype (typego_to_typlist env tg)

let typeret_to_gotype env tr = match tr with 
  | Tretour tg -> typego_to_gotype env [tg]
  | Tretour_list lg -> typego_to_gotype env lg
  | Nonetype_ret -> typego_to_gotype env []
 

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


let rec check_duplicate (list : ident loc list) = match list with
  | [] -> false
  | (id, pos) :: l -> 
  if List.exists (fun (y,_) -> id = y) l
  then raise_error RedundantVariable pos
  else check_duplicate l


(* Expression *)
let rec type_expr env le_pos = 
    (* return  typ , expr, pos, bool *)
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
          with Not_found -> raise_error (Notfound_ident name) pos
      end
      |Eident "_" -> (Tsimpl Tvoid, Eident "_", pos, false)
      | Eident _ -> assert false
      |Eunop (unop, te) -> begin 
        let t,e,p,b1 = type_expr env te in
        match unop with 
          | Not -> begin
            if t <> Tsimpl Tbool then raise_error (Expectedboolgot  t) pos
            else (Tsimpl Tbool, Eunop(Not, (e,p)), pos, false) end
          | Sign -> begin 
            if t <> Tsimpl Tint then raise_error (Expectedintgot  t) pos
            else (Tsimpl Tint, Eunop(Sign, (e,p)), pos, false) end
          | Address -> begin match (t,e,p,b1) with
              | (Tsimpl ta, expr, _, true) -> (Tsimpl (Tstar ta), Eunop(Address, (e,p)), pos, false)
              | (Tsimpl ta, _,_,_) ->raise_error Leftvalue pos 
              | (Tmany _,_,_,_) -> raise_error Tsimplrequired pos
            end 
          | Pointer -> begin
            if t = Tsimpl Tnone then raise_error PointerMissing pos
            else if b1 = true then raise_error Leftvalue pos 
            else begin match t with
                 | Tsimpl Tstar ta -> (Tsimpl ta , Eunop(Pointer, (e,p)), pos, true)
                 | _ -> raise_error Invalidargument pos end 
            end
        end
      |Ebinop(binop, e1, e2) -> begin
        let t1,exp1, p1,b1 = type_expr env e1 in 
        let t2,exp2, p2,b2 = type_expr env e2 in
        match binop with
          | And | Or -> begin match t1, t2 with 
            | Tsimpl Tbool, Tsimpl Tbool -> Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos,false
            | _, Tsimpl Tbool -> raise_error (Expectedboolgot t1) p1
            | _, _ -> raise_error (Expectedboolgot t2) p2 end
          | Add| Minus| Mult| Div|Mod -> begin match t1, t2 with 
            | Tsimpl Tint, Tsimpl Tint -> Tsimpl Tint, Ebinop(binop, (exp1,p1), (exp2,p2)),pos,false
            | _, Tsimpl Tint -> raise_error (Expectedintgot t1) p1
            | _, _ -> raise_error (Expectedintgot t2) p2 end
          | Lt | Leq |Gt|Geq -> begin match t1, t2 with 
            | Tsimpl Tint, Tsimpl Tint -> Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false
            | _, Tsimpl Tint -> raise_error (Expectedintgot t1) p1
            | _, _ -> raise_error (Expectedboolgot t2) p2 end
          | Iseq | Neq -> begin match t1, t2 with 
            | Tsimpl (Tstar Tnone), Tsimpl (Tstar Tnone) -> raise_error CantCompareNil pos 
            | Tsimpl (Tstar Tnone), Tsimpl (Tstar _) | Tsimpl (Tstar _), Tsimpl (Tstar Tnone)-> 
                (Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false) 
            | t1, t2 when t1 = t2 -> (Tsimpl Tbool, Ebinop(binop, (exp1,p1), (exp2,p2)),pos, false) 
            | _,_ -> raise_error (UnequalTypes (t1,t2)) pos end
      end 
      | Emethod(e, id) -> begin match type_expr env e with 
        | (Tsimpl (Tstruct s), expr, p, left) 
        | (Tsimpl (Tstar (Tstruct s)), expr, p, left) -> 
        begin 
          try let ts = Smap.find s env.structs in 
            try let tid = Smap.find id ts in 
                (Tsimpl tid, Emethod((expr,p), id), pos, left)
            with Not_found -> raise_error (Notfound_ident id) pos
          with Not_found -> raise_error (Notfound_struct s) pos  
        end 
        | (t,_,_,_) -> raise_error (Expectedstructgot t) pos
      end 
      | Eprint le -> begin 
            let rec help_unwrap = function 
              |[] -> [],[],[]
              |(a,b,c,d)::l2 ->  let la,lb,lc = help_unwrap l2 in 
              a::la,(b,c)::lb,d::lc
            in 
            let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
            (Tsimpl Tnone, Eprint exprs, pos, false)
            end
      | Ecall (id, le) ->  try begin
            let tinputs, tout = Smap.find id env.funct in
            let rec help_unwrap = function 
                |[] -> [],[],[]
                |(a,b,c,d)::l2 ->  let la,lb,lc = help_unwrap l2 in 
                a::la,(b,c)::lb,d::lc
            in 
            let types, exprs, _  = help_unwrap (List.map (type_expr env) le) in
            match tinputs, gotypelist_to_gotype types [] with
            | t1, t2 when t1 = t2 -> (tout, Ecall (id, exprs), pos, false)
            | _ -> raise_error Invalidargument pos
          end
          with Not_found -> raise_error (Notfound_funct id) pos 
      | _ -> assert false

let check_return_no_underscore exp =
  match exp with
  | Eident "_" -> true
  | _ -> false

let rec compare t1 t2 pos = match t1, t2 with 
  |  Tsimpl a, Tsimpl b when a = b -> true
  |  Tmany (a :: x), Tmany (b :: y) when a = b ->  compare (Tmany x) (Tmany y) pos
  | _,_ -> raise Typing_error

let rec help_unwrap = function 
    |[] -> [],[],[]
    |(a,b,c,d)::l2 ->  let la,lb,lc = help_unwrap l2 in 
    a::la,(b,c)::lb,d::lc

(* instructions *)
(* type_instruction -> returns env, tree, bool to say if it returned smthing and a bool to say if it printed something. *)
and type_instruction env trets = function 
  | Iblock (b, pos_b) -> 
    let env, tree, rb, pb =
    List.fold_left (fun (env, tree, rb, pb) (v, pos) -> 
      let ev, tr, retb, prb = type_instruction env trets v in
      ev, (tr, pos) :: tree, rb && retb, prb || pb) 
      (env, [], true, false) b 
    in  
    env, Iblock (List.rev tree, pos_b), rb, pb
  | _ -> assert false


(* functs *)
let add_function_to_env env d = match d with
  | Dstruct _ -> env
  | Dfunc ((id, vars, (trets, tpos), b),pos) ->
    if Smap.mem id env.funct then raise_error (RedundantFunctionName id) pos
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
        raise Typing_error      
    end

let add_struct_to_env env d = match d with
  | Dfunc _ -> env
  | Dstruct ((id, vars),pos) ->
    if Smap.mem id env.structs then raise_error (RedundantStructName) pos
    else 
    begin
      let ids_gtpos = List.fold_left (fun vs var -> 
        let (ids, _), pos = var in 
        (List.map (fun id -> (id, pos)) ids) @ vs)
        [] vars in
      if not( check_duplicate ids_gtpos ) then 
      begin
        let newStruct = List.fold_left (fun s (((ids, tau), pos) : Go_ast.vars loc) ->
          let tau = typego_to_typ env tau in 
          List.fold_left (fun s id -> Smap.add id tau s) s ids) Smap.empty vars in
        { env with structs = Smap.add id newStruct env.structs }
      end
      else
        raise Typing_error      
    end

(** Check that function is well-typed**)
let type_function env ((id, vars, (trets, tpos), block),pos) =
  let (tin, tout) = Smap.find id env.funct in
  let newmaxime = List.fold_left (fun s (((ids, tau), pos) : Go_ast.vars loc) ->
          let tau = typego_to_typ env tau in 
          List.fold_left (fun s id -> Smap.add id tau s) s ids) Smap.empty vars in
  let block = Iblock block in
  type_instruction {env with vars = newmaxime} trets block


let type_prog prog = 
let env = { structs= Smap.empty; funct = Smap.empty ; vars = Smap.empty }  in
  let env = List.fold_left add_struct_to_env env prog in
  let env = List.fold_left add_function_to_env env prog in
  let rec read_function is_print = function
    | [] -> is_print,[]
    | (Dstruct _)::l -> read_function is_print l
    | (Dfunc f)::l -> let env, tree, rb, pb = type_function env f in
      if not(rb) then raise Typing_error;
      let (bb,ll) = read_function (is_print || pb) l in
      (bb, tree::ll) 
  in
  let (is_print, functions) = read_function false prog in
  if not is_print then raise Typing_error;
  env, functions