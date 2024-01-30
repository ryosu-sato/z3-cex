open Util
open Ast_util
open CHC

module Dbg = Debug.Make (struct
  let check = Debug.make_check __MODULE__
end)

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

let reconstruct context (CHC rules) cex =
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

let parse_cex s =
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
