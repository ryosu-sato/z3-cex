open Util
module SMTLIB = Smtlib_utils.V_2_6

module Ast = struct
  include SMTLIB.Ast

  let var x = Const x

  let int n =
    if n >= 0 then Const (string_of_int n)
    else Arith (Minus, [ Const (string_of_int (-n)) ])

  let leq t1 t2 = Arith (Leq, [ t1; t2 ])
  let ( <= ) = leq
  let lt t1 t2 = Arith (Lt, [ t1; t2 ])
  let ( < ) = lt
  let geq t1 t2 = Arith (Geq, [ t1; t2 ])
  let ( >= ) = geq
  let gt t1 t2 = Arith (Gt, [ t1; t2 ])
  let ( > ) = gt
  let ( = ) = eq
  let add ts = Arith (Add, ts)
  let ( + ) t1 t2 = add [ t1; t2 ]
  let mult ts = Arith (Mult, ts)
  let ( * ) t1 t2 = mult [ t1; t2 ]
  let ( && ) t1 t2 = And [ t1; t2 ]
  let ( || ) t1 t2 = Or [ t1; t2 ]
  let and_ = function [] -> true_ | ts -> and_ ts
end

type env = (var * Ast.ty) list
and var = string
and term = Ast.term

let ty_int = Ast.Ty_app ("Int", [])

let eq_id x y =
  let strip s =
    if s.[0] = '|' then String.sub s 1 (String.length s - 2) else s
  in
  strip x = strip y

let is_var x =
  not
    (Exception.not_raise int_of_string x
    || Exception.not_raise float_of_string x)

let var_of t =
  match t with
  | Ast.Const x when is_var x -> x
  | _ -> invalid_arg "%s" __FUNCTION__

let is_fun_ty (ty : Ast.ty) = match ty with Ty_arrow _ -> true | _ -> false

let is_base_ty (ty : Ast.ty) =
  ty = ty_int || ty = Ast.Ty_bool || ty = Ast.Ty_real

(*
let is_pred_ty (ty:Ast.ty) =
  match ty with
  | Ty_arrow _ -> true
  | Ty_bool -> true
  | _ -> false
 *)

let rec get_fv (t : term) =
  match t with
  | Ast.True -> []
  | Ast.False -> []
  | Ast.Const x -> if is_var x then [ x ] else []
  | Ast.Arith (_, ts) -> List.rev_flatten_map get_fv ts
  | Ast.App (f, ts) -> f :: List.rev_flatten_map get_fv ts
  | Ast.HO_app (t1, t2) -> get_fv t1 @@@ get_fv t2
  | Ast.Match (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.If (_, _, _) -> unsupported "%s" __FUNCTION__
  | Ast.Let (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Is_a (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Fun (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Eq (t1, t2) -> get_fv t1 @@@ get_fv t2
  | Ast.Imply (t1, t2) -> get_fv t1 @@@ get_fv t2
  | Ast.And ts -> List.rev_flatten_map get_fv ts
  | Ast.Or ts -> List.rev_flatten_map get_fv ts
  | Ast.Not t -> get_fv t
  | Ast.Distinct ts -> List.rev_flatten_map get_fv ts
  | Ast.Cast (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Forall (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Exists (_, _) -> unsupported "%s" __FUNCTION__
  | Ast.Attr (_, _) -> unsupported "%s" __FUNCTION__

let make_trans f =
  let rec trans (t : term) =
    match f trans t with
    | None -> (
        match t with
        | True -> t
        | False -> t
        | Const _ -> t
        | Arith (op, ts) -> Arith (op, List.map trans ts)
        | App (f, ts) -> App (f, List.map trans ts)
        | HO_app (t1, t2) -> HO_app (trans t1, trans t2)
        | Match (_, _) -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t
        | If (_, _, _) -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t
        | Let (defs, t1) -> Let (List.map (Pair.map_snd trans) defs, trans t1)
        | Is_a (_, _) -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t
        | Fun (_, _) -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t
        | Eq (t1, t2) -> Eq (trans t1, trans t2)
        | Imply (t1, t2) -> Imply (trans t1, trans t2)
        | And ts -> And (List.map trans ts)
        | Or ts -> Or (List.map trans ts)
        | Not t -> Not (trans t)
        | Distinct ts -> Distinct (List.map trans ts)
        | Cast (_, _) -> unsupported "%s(%a)" __FUNCTION__ Ast.pp_term t
        | Forall (bind, t) -> Forall (bind, trans t)
        | Exists (bind, t) -> Exists (bind, trans t)
        | Attr (t, attrs) -> Attr (trans t, attrs))
    | Some t -> t
  in
  trans

let id_sep = "!"

let decomp_id s =
  try
    let s1, s2 = String.rsplit s ~by:id_sep in
    (s1, Some (int_of_string s2))
  with _ -> (s, None)

let succ_id s =
  let s', id = decomp_id s in
  let id' = Option.map_default succ 1 id in
  Format.sprintf "%s%s%d" s' id_sep id'

let rec gen_fresh xs y = if List.mem y xs then gen_fresh xs (succ_id y) else y

let gen_freshs xs ys =
  List.fold_left
    (fun (xs, acc_rev) y ->
      let y' = gen_fresh xs y in
      (y' :: xs, y' :: acc_rev))
    (xs, []) ys
  |> snd |> List.rev

let decomp_var t =
  match t with Ast.Const x -> x | _ -> invalid_arg "%s" __FUNCTION__

let decomp_app t =
  match t with Ast.App (f, ts) -> (f, ts) | _ -> invalid_arg "%s" __FUNCTION__

(** Non-capture-avoiding substitutions *)
let subst x t1 =
  let aux _tr t =
    match t with Ast.Const y when x = y -> Some t1 | _ -> None
  in
  make_trans aux

let subst_map map =
  make_trans (fun _tr t ->
      match t with
      | Ast.Const y when List.mem_assoc y map -> Some (List.assoc y map)
      | _ -> None)

let rename_map map =
  make_trans (fun tr (t : term) ->
      match t with
      | App (f, ts) when List.mem_assoc f map ->
          Some (App (List.assoc f map, List.map tr ts))
      | Const y when List.mem_assoc y map -> Some (Const (List.assoc y map))
      | _ -> None)

let rec decomp_and t =
  match t with Ast.And ts -> List.flatten_map decomp_and ts | _ -> [ t ]

let rec decomp_or t =
  match t with Ast.Or ts -> List.flatten_map decomp_or ts | _ -> [ t ]

let rec decomp_forall t =
  match t with
  | Ast.Forall (vars, t') ->
      let vars', t'' = decomp_forall t' in
      (vars @ vars', t'')
  | _ -> ([], t)

let rec decomp_exists t =
  match t with
  | Ast.Exists (vars, t') ->
      let vars', t'' = decomp_exists t' in
      (vars @ vars', t'')
  | _ -> ([], t)

let rec is_simple (t : term) =
  match t with
  | True | False | Const _ | App _ | Arith _ | Eq _ -> true
  | Not t -> is_simple t
  | _ -> false

let rec convert2cnf (t : term) : term list list =
  let make_or cnf1 cnf2 =
    Combination.product cnf1 cnf2 |> List.map (Fun.uncurry ( @ ))
  in
  match t with
  | True -> []
  | False -> [ [] ]
  | _ when is_simple t -> [ [ t ] ]
  | And _ ->
      let ts = decomp_and t in
      List.flatten_map convert2cnf ts
  | Or _ ->
      let ts = decomp_or t in
      List.fold_right (make_or -| convert2cnf) ts [ [] ]
  | _ ->
      Format.eprintf "%a@." Ast.pp_term t;
      unsupported "%s" __FUNCTION__

let push_not_into (t : term) : term =
  (* (aux true t <=> not t) and (aux false t <=> t)*)
  let rec aux flip (t : term) =
    match t with
    | And _ ->
        decomp_and t
        |> List.map (aux flip)
        |> if flip then Ast.or_ else Ast.and_
    | Or _ ->
        decomp_or t |> List.map (aux flip) |> if flip then Ast.and_ else Ast.or_
    | Not t -> aux (not flip) t
    | Forall (vars, t) ->
        (if flip then Ast.exists else Ast.forall) vars (aux flip t)
    | Exists (vars, t) ->
        (if flip then Ast.forall else Ast.exists) vars (aux flip t)
    | Imply (t1, t2) ->
        if flip then And [ aux false t1; aux true t2 ]
        else Or [ aux true t1; aux false t2 ]
    | Let (binds, t) -> aux flip (subst_map binds t)
    | _ when is_simple t -> if flip then Ast.Not t else t
    | _ ->
        Format.eprintf "%a@." Ast.pp_term t;
        unsupported "%s" __FUNCTION__
  in
  aux false t

let inline_let =
  make_trans (fun tr t ->
      match t with
      | Ast.Let (defs, t1) ->
          let defs' = List.map (Pair.map_snd tr) defs in
          Some (subst_map defs' @@ tr t1)
      | _ -> None)

let remove_attributes =
  make_trans (fun tr t ->
      match t with Ast.Attr (t, _) -> Some (tr t) | _ -> None)

let check_fv loc genv env t =
  let fv = get_fv t in
  let fv' =
    fv
    |> List.filter_out (List.mem_assoc -$- env)
    |> List.filter_out (List.mem_assoc -$- genv)
  in
  if fv' = [] then ()
  else (
    Format.printf "[check_fv] loc: %s@." loc;
    Format.printf "[check_fv] t: %a@." Ast.pp_term t;
    Format.printf "[check_fv] Dom(env): %a@."
      Print_.(list string)
      (List.map fst env);
    Format.printf "[check_fv] fv': %a@." Print_.(list string) fv';
    assert false)

let decomp_ty_arrow = function
  | Ast.Ty_arrow (tys, ty') -> (tys, ty')
  | ty -> ([], ty)

let decl_of_env env =
  env
  |> List.map (fun (f, ty) ->
         let tys, ty' = decomp_ty_arrow ty in
         Ast.decl_fun ~tyvars:[] f tys ty')

let insert_assert_before_check_sat asserts context =
  let count =
    List.count
      (function { Ast.stmt = Ast.Stmt_check_sat } -> true | _ -> false)
      context
  in
  match count with
  | 0 -> context @ asserts
  | 1 ->
      context
      |> List.flatten_map (fun stmt ->
             match stmt.Ast.stmt with
             | Ast.Stmt_check_sat -> asserts @ [ stmt ]
             | _ -> [ stmt ])
  | _ -> unsupported "%s" __FUNCTION__

let rec insert_decls_before_first_decl decls context =
  match context with
  | [] -> decls
  | { Ast.stmt = Stmt_decl _ } :: _ -> decls @ context
  | stmt :: context' -> stmt :: insert_decls_before_first_decl decls context'

let make_bool b = Ast.Const (string_of_bool b)

let make_int n : term =
  if n >= 0 then Const (string_of_int n)
  else Arith (Minus, [ Const (string_of_int (-n)) ])

let rec int_of_const (t : term) =
  match t with
  | Const n -> ( try int_of_string n with _ -> invalid_arg "%s" __FUNCTION__)
  | Arith (Minus, [ t1 ]) -> -int_of_const t1
  | _ -> invalid_arg "%s" __FUNCTION__

let rec eval (t : term) =
  let eval_int = int_of_const -| eval in
  let op_of (op : Ast.arith_op) =
    match op with
    | Leq -> ( <= )
    | Lt -> ( < )
    | Geq -> ( >= )
    | Gt -> ( > )
    | _ -> invalid_arg "%s" __FUNCTION__
  in
  match t with
  | Const _ -> t
  | Arith (((Leq | Lt | Geq | Gt) as op), [ t1; t2 ]) ->
      make_bool (op_of op (eval_int t1) (eval_int t2))
  | Arith (Add, ts) -> make_int (List.sum @@ List.map eval_int ts)
  | Arith (Minus, [ t1 ]) -> make_int (-eval_int t1)
  | Arith (Minus, [ t1; t2 ]) -> make_int (eval_int t1 - eval_int t2)
  | Arith (Mult, ts) -> make_int (List.mult @@ List.map eval_int ts)
  | _ -> invalid_arg "%s" __FUNCTION__

let simplify =
  let rec aux tr (t : term) =
    let rec_app t =
      let t' = tr t in
      aux tr t' |> Option.default t' |> Option.some
    in
    match t with
    | Arith _ when Exception.not_raise eval t -> Some (eval t)
    | Arith (Mult, Const "0" :: _) -> Some (Ast.Const "0")
    | Arith (Mult, [ Const "1"; t ]) -> rec_app t
    | Arith (Mult, Const "1" :: ts) -> rec_app @@ Ast.Arith (Mult, ts)
    | Arith (Add, [ Const "0"; t ]) -> rec_app t
    | Arith (Add, Const "0" :: ts) -> rec_app @@ Ast.Arith (Add, ts)
    | _ -> None
  in
  make_trans aux

let pp_stmts fm stmts =
  Format.fprintf fm "@[";
  List.iter (Format.fprintf fm "%a@\n" SMTLIB.Ast.pp_stmt) stmts;
  Format.fprintf fm "@]"

let pp_env fm env =
  let pr fm (x, ty) = Format.fprintf fm "%s:%a" x Ast.pp_ty ty in
  print_list pr ", " fm env

let ty_of_value (t : term) =
  match t with
  | True | False -> Ast.ty_bool
  | Arith (Minus, _) -> ty_int
  | Const x when Exception.not_raise int_of_string x -> ty_int
  | Const x when Exception.not_raise float_of_string x -> Ast.ty_real
  | _ -> unsupported "%s" __FUNCTION__

module Print = struct
  include Print_

  let var = string
  let term = Ast.pp_term
  let ty = Ast.pp_ty
  let stmts = pp_stmts
  let env = pp_env
end

module Ty = struct
  let int = ty_int
  let bool = Ast.ty_bool
  let real = Ast.ty_real
end
