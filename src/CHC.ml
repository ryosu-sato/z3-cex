open Util
open Ast_util

module Dbg = Debug.Make (struct
  let check = Debug.make_check __MODULE__
end)

type result = Sat of solution | Unsat of counterexample
and solution = (var * term) list
and counterexample = (int * (term * int list)) list

type solver = Z3 | Eldarica

type chc = CHC of rule list
and echc = E_CHC of env * rule list (* Outermost existensial *)

and ehchc =
  | EH_CHC of env * rule list (* Outermost existensial with disjunctive heads *)

and dhchc =
  | DH_CHC of
      env
      * rule list (* Outermost existensial with disjunctive/existential heads *)

and rule = { env : env; head : head; body : term list }

and head =
  | Bottom
  | App of var * term list
  | Exists of env * head
  | Disj of head list

let rec pp_head fm head =
  match head with
  | Bottom -> Format.fprintf fm "false"
  | App (f, ts) -> Format.fprintf fm "%a" Print.term (Ast.App (f, ts))
  | Exists (env, head) ->
      Format.fprintf fm "exists %a. %a" Print.env env pp_head head
  | Disj heads -> Format.fprintf fm "%a" (print_list pp_head " \\/") heads

let pp_rules fm rules =
  let pr fm { head; body } =
    Format.fprintf fm "@[<hov 4>%a :-@ @[%a@].@]" pp_head head
      (print_list Print.term ",@ ")
      body
  in
  Format.fprintf fm "@[";
  print_list pr "@\n" Format.std_formatter rules;
  Format.fprintf fm "@]"

let pp_env fm env =
  let pr fm (x, ty) = Format.fprintf fm "@[%s:%a@]" x Print.ty ty in
  List.print pr fm env

let pp_chc fm (CHC rules) = Format.fprintf fm "@[CHC@  @[%a@]@]" pp_rules rules

let pp_echc fm (E_CHC (env, rules)) =
  Format.fprintf fm "@[E_CHC%a@  @[%a@]@]" pp_env env pp_rules rules

let pp_ehchc fm (EH_CHC (env, rules)) =
  Format.fprintf fm "@[EH_CHC%a@  @[%a@]@]" pp_env env pp_rules rules

let pp_dhchc fm (DH_CHC (env, rules)) =
  Format.fprintf fm "@[DH_CHC%a@  @[%a@]@]" pp_env env pp_rules rules

let pp_cex fm (cex : counterexample) =
  let pr fm (n, (p, ns)) =
    Format.fprintf fm "@[[%d] %a :- %a@]" n Print.term p
      (print_list Format.pp_print_int ", ")
      ns
  in
  print_list pr "@\n" fm cex

let parse_cex_eld s =
  let aux s0 =
    try
      let n, s1 = String.split s0 ~by:": " in
      let n = int_of_string n in
      let s2, ns =
        try String.split s1 ~by:" -> " with
        | Not_found -> (s1, "")
        | _ -> assert false
      in
      let ns =
        match String.split_on_string ns ~by:", " with
        | [ "" ] -> []
        | ss -> List.map int_of_string ss
      in
      let p =
        if s2 = "FALSE" then Ast.False
        else
          match String.split ~by:"(" s2 with
          | exception Not_found -> Ast.Const s2
          | f, args ->
              assert (String.last args = ')');
              let args =
                args |> String.rchop
                |> String.split_on_string ~by:", "
                |> List.map
                     SMTLIB.(
                       fun s ->
                         Parser.parse_term Lexer.token (Lexing.from_string s))
              in
              Ast.App (f, args)
      in
      Some (n, (p, ns))
    with _ -> None
  in
  s |> String.split_on_char '\n' |> List.filter_map aux

let make_genv stmts =
  List.L.filter_map stmts ~f:(fun stmt ->
      match stmt.Ast.stmt with
      | Ast.Stmt_decl { fun_args = []; fun_name; fun_ret } ->
          Some (fun_name, fun_ret)
      | Ast.Stmt_decl { fun_args; fun_name; fun_ret } ->
          Some (fun_name, Ast.Ty_arrow (fun_args, fun_ret))
      | _ -> None)

let decomp_exists_stmts (stmts : Ast.statement list) =
  List.L.partition_map stmts ~f:(fun stmt ->
      match stmt.Ast.stmt with
      | Ast.Stmt_decl { fun_name; fun_ret } when fun_ret <> Ty_bool ->
          Left (fun_name, fun_ret)
      | _ -> Right stmt)

let rec head_of_term (t : term) : head =
  match t with
  | False -> Bottom
  | Const f -> App (f, [])
  | App (f, ts) -> App (f, ts)
  | Exists (env, t) -> Exists (env, head_of_term t)
  | _ ->
      Format.printf "%a@." Print.term t;
      assert false

let rec term_of_head head : term =
  match head with
  | Bottom -> False
  | App (f, []) -> Const f
  | App (f, ts) -> App (f, ts)
  | Exists (env, head) -> Exists (env, term_of_head head)
  | Disj heads -> Or (List.map term_of_head heads)

let unify_term (t1 : term) (t2 : term) =
  if t1 = t2 then Some []
  else
    match (t1, t2) with
    | Const f, Const g when eq_id f g -> Some []
    | App (f, ts1), App (g, ts2) when eq_id f g -> Some (List.combine ts1 ts2)
    | _ -> None

let map_head f head = head |> term_of_head |> f |> head_of_term

let map_rule f { env; head; body } =
  { env; head = map_head f head; body = List.map f body }

let predicates_of (CHC rules) =
  rules
  |> List.rev_flatten_map (fun { env; head; body } ->
         get_fv (term_of_head head) @@@ List.rev_flatten_map get_fv body
         |> List.filter_out (List.mem_assoc -$- env))

type env = Env of (var * (term * env)) list
type unsat_proof = (int * (term * int list)) list

let construct_proof_tree t =
  let counter = ref 0 in
  let cache = ref [] in
  let rec loop (Env env) (t : term) : int * unsat_proof =
    match t with
    | Const x ->
        let t, env' = List.assoc x env in
        loop env' t
    | Let (defs, t1) ->
        let env' =
          Env (List.map (Pair.map_snd (Pair.pair -$- Env env)) defs @@@ env)
        in
        loop env' t1
    | App ("_hyper-res_", ts) ->
        let ts', head = List.decomp_snoc @@ List.tl ts in
        if List.mem_assoc head !cache then (List.assoc head !cache, [])
        else
          let i = !counter in
          incr counter;
          let indices, proofss = List.split_map (loop (Env env)) ts' in
          cache := (head, i) :: !cache;
          (i, (i, (head, indices)) :: List.flatten proofss)
    | App ("mp", [ t1; Imply (goal, False); False ]) ->
        let i, proofs = loop (Env env) t1 in
        ( i,
          List.map
            (fun (i, (t, indices)) ->
              if t = goal then (i, (Ast.False, indices)) else (i, (t, indices)))
            proofs )
    | _ ->
        Format.printf "%a@." Print.term t;
        assert false
  in
  snd @@ loop (Env []) t

let copy_rule fv ({ env } as rule) =
  let fv' = List.rev_map_append fst env fv in
  let xs = gen_freshs fv' @@ List.map fst env in
  let env' = List.map2 (fun x (_, ty) -> (x, ty)) xs env in
  let map = List.map2 (fun (x, _) (y, _) -> (x, Ast.var y)) env env' in
  { (map_rule (subst_map map) rule) with env = env' }

let decomp_body env ts =
  List.partition
    (function
      | Ast.App _ -> true | Const x -> not (List.mem_assoc x env) | _ -> false)
    ts

let unify_rule fv target rule =
  let open Option in
  let { head; body; env } = copy_rule fv rule in
  (* Format.printf "[unify_rule] rule: %a@." pp_rules [rule]; *)
  (* Format.printf "[unify_rule] copied: %a@." pp_rules [{head;body;env}]; *)
  let* map = unify_term (term_of_head head) target in
  let map = List.map (Pair.map_fst var_of) map in
  let env = List.filter_out (fst |- List.mem_assoc -$- map) env in
  let apps, constr = decomp_body env (List.rev_map (subst_map map) body) in
  return (env, apps, constr)

exception Found of counterexample

let find preds (CHC rules) i i_next target =
  let rec loop targets (env, constr, sol) (i, cex) =
    (* Format.printf "targets: %a@." Print.(list (int * term)) targets; *)
    (* Format.printf "constr: %a@.@." Print.(list term) constr; *)
    match targets with
    | [] ->
        (* Format.printf "sol: %a@." Print.(list (var * term)) sol; *)
        (* Format.printf "cex: %a@." pp_cex @@ List.sort compare cex; *)
        let cex =
          cex |> List.sort compare
          |> List.map (Pair.map_snd (Pair.map_fst (subst_map sol |- simplify)))
        in
        Some cex
    | (j, target) :: targets' ->
        let fv = List.rev_map_append fst env preds in
        List.L.find_map_opt rules ~f:(fun rule ->
            let open Option in
            let* new_env, new_targets, new_constr = unify_rule fv target rule in
            (* Format.printf "matched: %a@.@." Print.term target; *)
            (* Format.printf "new_targets: %a@." Print.(list term) new_targets; *)
            let constr = new_constr @@@ constr in
            (* Format.printf "new_constr: %a@.@." Print.(list term) new_constr; *)
            let env = new_env @@@ env in
            let* sol =
              if new_constr = [] then return sol
              else Z3_interface.solve env constr |> Result.to_option
            in
            let new_targets_with =
              List.mapi (fun j t -> (i + j, t)) new_targets
            in
            let targets = new_targets_with @@@ targets' in
            let cex = (j, (target, List.map fst new_targets_with)) :: cex in
            let i = i + List.length new_targets in
            loop targets (env, constr, sol) (i, cex))
  in
  match loop [ (i, target) ] ([], [], []) (i_next, []) with
  | None -> assert false
  | Some cex -> cex

let parse_cex_z3 s =
  (* let ss = String.split_on_char '\n' s in *)
  (* List.iteri (Format.printf "%d: %s@.") ss; *)
  let s =
    Str.global_replace (Str.regexp "(_ hyper-res[^)]*)") "_hyper-res_" s
  in
  let proof =
    SMTLIB.Parser.parse_term SMTLIB.Lexer.token (Lexing.from_string s)
  in
  (* let tr = make_trans (fun tr t -> match t with App("hyper-res", ts) -> Some (App("hyper-res", Const "_"::List.tl (List.map tr ts)))| _ -> None) in *)
  let remove_asserted =
    make_trans (fun tr t ->
        match t with App ("asserted", [ t1 ]) -> Some (tr t1) | _ -> None)
  in
  let t = Ast_util.remove_attributes (remove_asserted proof) in
  (* Format.printf "t: %a@." Print.term t; *)
  let proof = construct_proof_tree t in
  (* Format.printf "cex: %a@." Print.term t; *)
  (* Format.printf "proof: %a@.@." Print.(list (int * (term * list int))) proof; *)
  proof

let reconstruct_counterexample_z3 context (CHC rules) cex =
  let postfix = "!" in
  let rename p = p ^ postfix in
  let renamed = String.ends_with -$- postfix in
  let preds =
    List.filter_map
      (function
        | { Ast.stmt = Stmt_decl { fun_name; fun_ret } } when fun_ret = Ty_bool
          ->
            Some fun_name
        | _ -> None)
      context
  in
  let aux (i', cache, acc) (_, (target, indices)) =
    (* Format.printf "target: %a@." Print.term target; *)
    match List.assoc target cache with
    | exception Not_found ->
        (* Format.printf "Not_found@.@."; *)
        (i', cache, acc)
    | i ->
        (* Format.printf "i: %d@." i; *)
        let ts = List.map (fun i -> List.assoc i cex |> fst) indices in
        (* Format.printf "FIND: %a -> %a@." Print.(list term) ts Print.term target; *)
        let map_inv, rules' =
          let preds =
            List.filter_map
              (function _, (Ast.App (f, _), _) -> Some f | _ -> None)
              cex
          in
          assert (not (List.exists renamed preds));
          let map = List.map (Pair.add_right rename) preds in
          let rules' =
            List.map
              (fun rule ->
                { rule with body = List.map (rename_map map) rule.body })
              rules
          in
          let new_rules =
            List.L.map ts ~f:(fun t ->
                let f, args = try decomp_app t with _ -> (var_of t, []) in
                let xs = gen_freshs preds @@ List.map (Fun.const "arg") args in
                let env = List.map2 (fun x v -> (x, ty_of_value v)) xs args in
                let head = App (rename f, List.map Ast.const xs) in
                let body = List.map2 (fun x v -> Ast.(var x = v)) xs args in
                { env; head; body })
          in
          (* Format.printf "rules': %a@." pp_chc (CHC rules'); *)
          (* Format.printf "new_rules: %a@." pp_chc (CHC new_rules); *)
          (List.map Pair.swap map, new_rules @@@ rules')
        in
        let cex = find preds (CHC rules') i i' target in
        let cex1, cex2 =
          List.partition
            (Exception.default false
               (snd |- fst |- decomp_app |- fst |- renamed))
            cex
        in
        (* Format.printf "i: %d@." i; *)
        (* Format.printf "i': %d@." i'; *)
        (* Format.printf "@[cex1: %a@]" pp_cex cex1; *)
        (* Format.printf "@[cex2: %a@." pp_cex cex2; *)
        let acc = cex2 @@@ acc in
        ( i' + List.length cex,
          List.map (fun (i, (t, _)) -> (rename_map map_inv t, i)) cex1 @@@ cache,
          acc )
  in
  let _, cache, cex = List.fold_left aux (1, [ (Ast.False, 0) ], []) cex in
  let map =
    let make xs =
      let x, xs' = List.find_decomp (List.mem_assoc -$- cex) xs in
      List.map (Pair.pair -$- x) xs'
    in
    cache
    |> List.classify ~eq:(Compare.eq_on fst)
    |> List.map (List.map snd)
    |> List.filter (List.length |- ( <= ) 2)
    |> List.map (List.sort compare)
    |> List.flatten_map make
  in
  (* Format.printf "map: %a@.@." Print.(list (int * int)) map; *)
  let cex =
    List.map
      (Pair.map_snd
         (Pair.map_snd (List.map (List.assoc_default_id ~eq:( = ) -$- map))))
      cex
  in
  (* Format.printf "cex: %a@.@." Print.(list (int * (term * list int))) cex; *)
  List.sort compare cex

let dhchc_of_statements stmts =
  let genv = make_genv stmts in
  let xs, stmts = decomp_exists_stmts stmts in
  let context, asserts =
    stmts
    |> List.partition_map (function
         | { Ast.stmt = Stmt_assert t } -> Right t
         | stmt -> Left stmt)
  in
  let context =
    Format.printf {|(warning "ignore after (check-sat)")@.|};
    let ctx1, ctx2 =
      List.takedrop_while
        (function { Ast.stmt = Stmt_check_sat } -> false | _ -> true)
        context
    in
    ctx1 @ [ List.hd ctx2 ]
  in
  let rules =
    asserts
    |> List.flatten_map (fun t ->
           let env, t = decomp_forall @@ push_not_into t in
           t |> convert2cnf
           |> List.map (fun conj ->
                  let pos, neg =
                    List.L.partition conj ~f:(function
                      | Ast.Const x -> not (List.mem_assoc x env)
                      | App _ | Exists _ | Or _ -> true
                      | _ -> false)
                  in
                  let head =
                    match pos with
                    | [] -> Bottom
                    | [ t ] -> head_of_term t
                    | _ -> Disj (List.map head_of_term pos)
                  in
                  let body =
                    List.L.map neg ~f:(function
                      | Ast.Not t -> t
                      | t -> Ast.Not t)
                  in
                  { env; head; body }))
  in
  (genv, context, DH_CHC (xs, rules))

let is_simple_head head =
  match head with Ast.False -> true | Ast.App _ -> true | _ -> assert false

let rec decomp_exists' head =
  match head with
  | Bottom -> ([], Bottom)
  | App _ -> ([], head)
  | Exists (env, head) ->
      let env', head' = decomp_exists' head in
      (env @ env', head')
  | Disj _ -> assert false

let echc_of_ehchc genv (EH_CHC (env, rules)) =
  let trans { env; head; body } (vars, new_env, rules) =
    let exists_env, head' = decomp_exists' head in
    let coefss, body' =
      let int_env = List.filter (snd |- ( = ) ty_int) env in
      let make (x, ty) =
        let coefs =
          List.map
            (fun (y, ty) -> (gen_fresh vars ("c_" ^ x ^ "_" ^ y), ty))
            int_env
        in
        let coef = gen_fresh vars ("c_" ^ x) in
        assert (not (List.mem_assoc coef coefs));
        (* TODO: Fix *)
        let t =
          let lin =
            Ast.(
              add
                (Const coef
                :: List.map2
                     (fun (c, _) (y, _) -> mult [ Const c; Const y ])
                     coefs int_env))
          in
          match ty with
          | _ when ty = ty_int -> Ast.(Eq (Const x, lin))
          | Ast.Ty_bool -> Ast.(Eq (Const x, geq (Const "0") lin))
          | _ -> unsupported "exists for %a" Print.ty ty
        in
        ((coef, ty_int) :: coefs, t)
      in
      List.split_map make exists_env
    in
    let env = exists_env @ env in
    let head = head' in
    let body = body @ body' in
    ( List.flatten_map (List.map fst) coefss @@@ vars,
      List.fold_left (fun coef acc -> coef @@@ acc) new_env coefss,
      { env; head; body } :: rules )
  in
  let _, new_env, rules =
    let vars = List.map fst genv in
    List.fold_right trans rules (vars, [], [])
  in
  (new_env @@@ genv, E_CHC (new_env @@@ env, rules))

let ehchc_of_dhchc genv context (DH_CHC (env, rules)) =
  let rec normalize head =
    match head with
    | Bottom -> assert false
    | App (f, ts) -> ([], [ (f, ts) ])
    | Exists (env, head') ->
        let env', apps = normalize head' in
        (env @ env', apps)
    | Disj ts ->
        let envs, tss = List.split_map normalize ts in
        let env = List.flatten envs in
        assert (List.is_unique env);
        (env, List.flatten tss)
  in
  let vars = List.map fst genv in
  let trans { env; head; body } (vars, f_env, rules) =
    let vars, f_env, new_rules, head =
      if head = Bottom then (vars, f_env, [], head)
      else
        let env', apps = normalize head in
        let n = List.length apps in
        if n <= 1 then (vars, f_env, [], head)
        else
          let args = List.unique (List.flatten_map snd apps) in
          let arg_vars = List.map decomp_var args in
          let arg_env =
            List.filter (fst |- List.mem -$- arg_vars) (env' @ env)
          in
          let vars' = List.map fst env @@@ vars in
          let disj = gen_fresh vars' "Disj" in
          let f_ty =
            Ast.Ty_arrow
              (ty_int :: List.map (List.assoc_ -$- arg_env) arg_vars, Ty_bool)
          in
          let case = gen_fresh vars' "case" in
          let head =
            Exists (env' @ [ (case, ty_int) ], App (disj, Const case :: args))
          in
          let rules =
            apps
            |> List.mapi (fun i (g, ts) ->
                   let body =
                     let switch =
                       if i = 0 then Ast.(var case < int 0)
                       else if i = n - 1 then Ast.(var case >= int (n - 2))
                       else Ast.(var case = int (n - 3))
                     in
                     Ast.[ App (disj, var case :: args); switch ]
                   in
                   let head = App (g, ts) in
                   { env = (case, ty_int) :: arg_env; head; body })
          in
          (disj :: vars, (disj, f_ty) :: f_env, rules, head)
    in
    (vars, f_env, ({ env; head; body } :: new_rules) @@@ rules)
  in
  let _, f_env, rules = List.fold_right trans rules (vars, [], []) in
  let genv' = f_env @ genv in
  let context' = insert_decls_before_first_decl (decl_of_env f_env) context in
  (genv', context', EH_CHC (env, rules))

exception Clause_not_found

let args_of_head (t : term) =
  match t with
  | False -> []
  | Const _ -> []
  | App (_, ts) -> ts
  | _ -> assert false

let statement_of_rule { env; head; body } =
  Ast.(assert_ (forall env (imply (and_ body) (term_of_head head))))

let insert_rules rules context =
  let asserts = List.map statement_of_rule rules in
  insert_assert_before_check_sat asserts context

let add_cex_context stmt =
  let open Ast in
  [
    _mk (Stmt_set_option [ ":produce-proofs"; "true" ]);
    _mk (Stmt_set_option [ ":pp.pretty_proof"; "true" ]);
  ]
  @ stmt
  @ [ _mk Stmt_get_proof; _mk Stmt_exit ]

let solve ?(args = [||]) context (CHC rules) =
  let stmts = insert_rules rules context |> add_cex_context in
  let option = Array.to_list args |> String.join " " in
  Dbg.printf "@[[solve_chc] stmts@\n  %a@]" Print.stmts stmts;
  let@ cin, fmt = Command.open_z3 ~option () in
  Format.fprintf fmt "%a@." Print.stmts stmts;
  if false then Format.printf "%a@." Print.stmts stmts;
  match input_line cin with
  | "sat" -> `Sat ()
  | "unsat" ->
      let cex = parse_cex_z3 (IO.input_all cin) in
      let cex = reconstruct_counterexample_z3 context (CHC rules) cex in
      `Unsat cex
  | s ->
      Format.eprintf "%s@." s;
      assert false

module Print = struct
  include Print

  let rules = pp_rules
  let env = pp_env
  let chc = pp_chc
  let echc = pp_echc
  let ehchc = pp_ehchc
  let dhchc = pp_dhchc
  let cex = pp_cex
end
