(** Core IR for source language S, in strict A-normal form (ANF). *)

type var = string
type tag = string
type prim = string

type atom =
  | AInt of int
  | AVar of var

type rhs =
  | Atom of atom
  | Prim of prim * atom list

type pat = PTag of tag * var list

type cmd =
  | Return of atom
  | Let of var * rhs * Label.t
  | LetCall of var * var * atom list * Label.t
  | LetTag of var * tag * atom list * Label.t
  | Match of atom * (pat * Label.t) list

type fundef = { name : var; params : var list; entry : Label.t }

type program = {
  funs : fundef list;
  ctrl : cmd Label.Map.t;
  main : Label.t;
}

let cmd_at (p : program) (l : Label.t) : cmd =
  match Label.Map.find_opt l p.ctrl with
  | Some c -> c
  | None ->
      invalid_arg
        (Printf.sprintf "S_syntax.cmd_at: no command at %s" (Label.to_string l))

let ctrl_of_list (pairs : (Label.t * cmd) list) : cmd Label.Map.t =
  List.fold_left (fun m (l, c) -> Label.Map.add l c m) Label.Map.empty pairs
