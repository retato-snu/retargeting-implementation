(** Permissive surface AST for the source language S, before A-normalization. *)

exception Parse_error of string

type expr =
  | Int of int
  | Var of string
  | App of string * expr list

type cmd =
  | Return of expr
  | Let of string * expr * cmd
  | Match of string * (pat * cmd) list

and pat = string * string list

type fundef = { name : string; params : string list; body : cmd }

type program = { funs : fundef list; main : cmd }
