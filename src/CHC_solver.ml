open Util
open Ast_util
open CHC

let add_cex_context stmt =
  let open Ast in
  [
    _mk (Stmt_set_option [ ":produce-proofs"; "true" ]);
    _mk (Stmt_set_option [ ":pp.pretty_proof"; "true" ]);
  ]
  @ stmt
  @ [ _mk Stmt_get_proof; _mk Stmt_exit ]

let solve ?(args = [||]) genv context chc =
  let (CHC rules) = normalize_head_args genv chc in
  let stmts = insert_rules rules context |> add_cex_context in
  let option = Array.to_list args |> String.join " " in
  Dbg.printf "@[[solve_chc] stmts@\n  %a@]" Print.stmts stmts;
  let@ cin, fmt = Command.open_z3 ~option () in
  Format.fprintf fmt "%a@." Print.stmts stmts;
  if false then Format.printf "%a@." Print.stmts stmts;
  match input_line cin with
  | "sat" -> `Sat ()
  | "unsat" ->
      let cex = Unsat_proof.parse_cex (IO.input_all cin) in
      let cex = Unsat_proof.reconstruct context (CHC rules) cex in
      `Unsat cex
  | s ->
      Format.eprintf "%s@." s;
      assert false
