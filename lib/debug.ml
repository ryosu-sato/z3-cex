open Util

let print ?(out = BatIO.stdout) x = BatPervasives.print_any out x

module type COND = sig
  val check : unit -> bool
end

module type DEBUG = sig
  val force : bool option ref
  val on : unit -> unit
  val off : unit -> unit
  val reset : unit -> unit
  val check : unit -> bool
  val set_default_formatter : Format.formatter -> unit

  val kfprintf :
    (Format.formatter -> 'a) ->
    Format.formatter ->
    ('b, Format.formatter, unit, 'a) format4 ->
    'b

  val printf : ('a, Format.formatter, unit) format -> 'a
  val eprintf : ('a, Format.formatter, unit) format -> 'a
  val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val exec : (unit -> unit) -> unit
  val tfprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val tprintf : ('a, Format.formatter, unit) format -> 'a
end

module Make (Cond : COND) : DEBUG = struct
  let force = ref None
  let on () = force := Some true
  let off () = force := Some false
  let reset () = force := None
  let check () = match !force with Some b -> b | _ -> Cond.check ()
  let default_formatter = ref Format.std_formatter
  let set_default_formatter fm = default_formatter := fm

  let kfprintf k fm f =
    if check () then Format.kfprintf k fm f else Format.ikfprintf k fm f

  let fprintf fm f =
    if check () then Format.fprintf fm f else Format.ifprintf fm f

  let printf f = fprintf !default_formatter f
  let eprintf f = fprintf Format.err_formatter f
  let exec f = if check () then f ()
  let tfprintf ppf f = fprintf ppf ("[%.3f] " ^^ f) !!Time.get
  let tprintf f = tfprintf Format.std_formatter f
end

let get_debug_param () =
  try Sys.getenv "DEBUG" |> String.split_on_char ',' with Not_found -> []

let is_in_debug_param s = List.mem s !!get_debug_param

let make_check module_name =
  let m = String.remove_prefix_if_any ~prefix:"Dune__exe__" module_name in
  Fun.const (is_in_debug_param m)
