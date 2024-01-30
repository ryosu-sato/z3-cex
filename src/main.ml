open Util
module Print = CHC.Print
module SMTLIB = Smtlib_utils.V_2_6
module Ast = SMTLIB.Ast

module Dbg = Debug.Make (struct
  let check = Debug.make_check __MODULE__
end)

let main filename args =
  let stmts = SMTLIB.parse_file_exn filename in
  let genv, context, dhchc = CHC.dhchc_of_statements stmts in
  let genv, context, ehchc = CHC.ehchc_of_dhchc genv context dhchc in
  let genv, E_CHC (env, rules) = CHC.echc_of_ehchc genv ehchc in
  assert (env = []);
  match CHC_solver.solve ~args genv context (CHC rules) with
  | `Sat _ -> `Sat
  | `Unsat cex -> `Unsat cex

let print_usage () =
  Format.printf "z3-cex v0.1@.";
  Format.printf "  Usage: z3-cex input.smt2 [options of z3]@."

let () =
  if Array.length Sys.argv < 2 then (
    print_usage ();
    exit 1)
  else
    let () = Format.set_margin 120 in
    let options = Array.sub Sys.argv 2 (Array.length Sys.argv - 2) in
    match main Sys.argv.(1) options with
    | `Sat -> Format.printf "sat@."
    | `Unsat cex ->
        Format.printf "unsat@.@.";
        Format.printf "%a@." Print.cex cex
