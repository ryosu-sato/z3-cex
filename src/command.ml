open Util

let z3 = "z3"

let open_z3 ?(option = "") () cont =
  let@ cin, cout =
    Unix.CPS.open_process (Format.sprintf "%s %s -in" z3 option)
  in
  let fmt = Format.formatter_of_out_channel cout in
  cont (cin, fmt)
