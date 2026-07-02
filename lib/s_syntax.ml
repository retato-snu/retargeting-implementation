(** S: core IR for the source language, in relaxed A-normal form (main.tex l.240-298). *)

exception Parse_error of string

type var = string
type tag = string
type prim = string

type exp =
  | EInt of int
  | EVar of var
  | EPrim of prim * exp list (* o(ē) *)
  | ETag of Label.t * tag * exp list (* T(ē); the Label.t is the allocation site *)

type pat = PTag of tag * var list

type cmd =
  | Return of exp
  | Let of var * exp * Label.t
  | LetCall of var * var * exp list * Label.t
  | Match of exp * (pat * Label.t) list

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
