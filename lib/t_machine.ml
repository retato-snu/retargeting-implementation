(** T's abstract machine, transcribed from the paper's calculated T-machine; runs directly on the T abstract syntax of {!T_encoding}. *)

open T_encoding

(* Arithmetic/conditional frames carry no env: the right operand/branch runs under the current env, sound by well-bracketedness; only [Let]/[App] save and restore it via [Restore]. *)
type frame =
  | Sub1 of expr
  | Sub2 of value
  | Mul1 of expr
  | Mul2 of value
  | Let of var_id * expr
  | App of fun_id
  | Ifz of expr * expr
  | Restore of env
  | Silent

type kont = frame list

type control =
  | Expr of expr
  | Value of value

type state = { control : control; env : env; kont : kont }

exception Stuck of string

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck s)) fmt

let env_lookup (rho : env) (x : var_id) : value =
  match List.assoc_opt x rho with
  | Some n -> n
  | None -> stuck "unbound variable %d" x

let fundef (ds : defs) (f : fun_id) : expr =
  match List.assoc_opt f ds with
  | Some body -> body
  | None -> stuck "undefined function %d" f

(** The implicit single parameter id, the paper's [x_arg]. *)
let x_arg : var_id = 0

type step_result =
  | Next of state
  | Done of value

let step (defs : defs) (s : state) : step_result =
  match s.control with
  | Expr e -> (
      match e with
      | Int (_, n) -> Next { s with control = Value n }
      | Var (_, x) -> Next { s with control = Value (env_lookup s.env x) }
      | Sub (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Sub1 e2 :: s.kont }
      | Mul (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Mul1 e2 :: s.kont }
      | Let (_, x, e1, e2) ->
          Next { s with control = Expr e1; kont = Let (x, e2) :: s.kont }
      | App (_, f, e1) ->
          Next { s with control = Expr e1; kont = App f :: s.kont }
      | Ifz (_, e1, e2, e3) ->
          Next { s with control = Expr e1; kont = Ifz (e2, e3) :: s.kont })
  | Value n -> (
      match s.kont with
      | [] -> Done n
      | Sub1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Sub2 n :: rest }
      | Sub2 n1 :: rest -> Next { s with control = Value (n1 - n); kont = rest }
      | Mul1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Mul2 n :: rest }
      | Mul2 n1 :: rest -> Next { s with control = Value (n1 * n); kont = rest }
      | Let (x, e2) :: rest ->
          Next
            {
              control = Expr e2;
              env = (x, n) :: s.env;
              kont = Restore s.env :: rest;
            }
      | App f :: rest ->
          Next
            {
              control = Expr (fundef defs f);
              env = [ (x_arg, n) ];
              kont = Restore s.env :: rest;
            }
      | Restore env :: rest -> Next { control = Value n; env; kont = rest }
      | Silent :: rest -> Next { s with kont = rest }
      | Ifz (e2, e3) :: rest ->
          let branch = if n = 0 then e2 else e3 in
          Next { s with control = Expr branch; kont = Silent :: rest })

let inject ?(arg : value = 0) (p : program) : state =
  { control = Expr p.main; env = [ (x_arg, arg) ]; kont = [] }

type outcome =
  | Final of value
  | OutOfFuel

let run_outcome ?(fuel = 1_000_000) ?(arg : value = 0) (p : program) : outcome =
  let rec loop n s =
    if n <= 0 then OutOfFuel
    else
      match step p.defs s with
      | Done v -> Final v
      | Next s' -> loop (n - 1) s'
  in
  loop fuel (inject ~arg p)

let run ?(fuel = 1_000_000) ?(arg : value = 0) (p : program) : value =
  match run_outcome ~fuel ~arg p with
  | Final v -> v
  | OutOfFuel -> failwith "T_machine.run: step budget exhausted"
