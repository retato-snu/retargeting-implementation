(** Program labels and the label-indexed control map.

    Labels are integers (reference [Label.L int] style). Interpreter points are
    extracted structurally, never by hardcoded numbers. *)

type t = int

let compare = Int.compare
let equal = Int.equal
let pp fmt l = Format.fprintf fmt "L%d" l
let to_string l = "L" ^ string_of_int l

module Map = Map.Make (Int)
module Set = Set.Make (Int)
