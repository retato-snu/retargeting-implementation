(** Concrete S C_aEK machine: executable reference semantics for the S core language. *)

type value =
  | VInt of int
  | VTag of S_syntax.tag * value list

module Env = Map.Make (String)

type env = value Env.t

(* A frame is the suspended LetCall's label plus the env to restore on return. *)
type frame = { suspended : Label.t; saved_env : env }

type kont = frame list

type state = { label : Label.t; env : env; kont : kont }

exception Stuck of string

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck s)) fmt

let lookup (rho : env) (x : S_syntax.var) : value =
  match Env.find_opt x rho with
  | Some v -> v
  | None -> stuck "unbound variable %s" x

let eval_atom (a : S_syntax.atom) (rho : env) : value =
  match a with
  | S_syntax.AInt n -> VInt n
  | S_syntax.AVar x -> lookup rho x

let eval_prim (o : S_syntax.prim) (args : value list) : value =
  let as_int op idx = function
    | VInt n -> n
    | VTag (t, _) ->
        stuck "primitive %s: argument %d expected int, got tag %s" op idx t
  in
  let bin op f =
    match args with
    | [ a; b ] -> VInt (f (as_int op 0 a) (as_int op 1 b))
    | _ ->
        stuck "primitive %s: expected 2 arguments, got %d" op (List.length args)
  in
  match o with
  | "sub" -> bin "sub" ( - )
  | "mul" -> bin "mul" ( * )
  | "iszero" -> (
      match args with
      | [ a ] -> if as_int "iszero" 0 a = 0 then VTag ("True", []) else VTag ("False", [])
      | _ ->
          stuck "primitive iszero: expected 1 argument, got %d"
            (List.length args))
  | _ -> stuck "unknown primitive %s" o

let eval_rhs (r : S_syntax.rhs) (rho : env) : value =
  match r with
  | S_syntax.Atom a -> eval_atom a rho
  | S_syntax.Prim (o, args) -> eval_prim o (List.map (fun a -> eval_atom a rho) args)

type step_result =
  | Next of state
  | Done of value

let rec step (p : S_syntax.program) (s : state) : step_result =
  match S_syntax.cmd_at p s.label with
  | S_syntax.Return a -> (
      let v = eval_atom a s.env in
      match s.kont with
      | [] -> Done v
      | { suspended; saved_env } :: rest -> (
          match S_syntax.cmd_at p suspended with
          | S_syntax.LetCall (x, _f, _args, l) ->
              Next { label = l; env = Env.add x v saved_env; kont = rest }
          | other ->
              stuck
                "S-Return: continuation frame does not suspend a LetCall (%s)"
                (cmd_name other)))
  | S_syntax.Let (x, r, l) ->
      let v = eval_rhs r s.env in
      Next { label = l; env = Env.add x v s.env; kont = s.kont }
  | S_syntax.LetCall (_x, f, args, _l) -> (
      (* [_x]/[_l] are recovered later by S-Return from the suspended label, not consumed here. *)
      match find_fun p f with
      | None -> stuck "LetCall: undefined function %s" f
      | Some def ->
          let arg_vals = List.map (fun a -> eval_atom a s.env) args in
          let callee_env =
            try
              List.fold_left2
                (fun e param v -> Env.add param v e)
                Env.empty def.S_syntax.params arg_vals
            with Invalid_argument _ ->
              stuck "LetCall: %s expects %d arguments, got %d" f
                (List.length def.S_syntax.params)
                (List.length arg_vals)
          in
          let frame = { suspended = s.label; saved_env = s.env } in
          Next
            {
              label = def.S_syntax.entry;
              env = callee_env;
              kont = frame :: s.kont;
            })
  | S_syntax.LetTag (x, t, args, l) ->
      let arg_vals = List.map (fun a -> eval_atom a s.env) args in
      let v = VTag (t, arg_vals) in
      Next { label = l; env = Env.add x v s.env; kont = s.kont }
  | S_syntax.Match (a, branches) -> (
      match eval_atom a s.env with
      | VInt n -> stuck "Match: scrutinee is an integer (%d), not a tag" n
      | VTag (t, vs) -> (
          match select_branch t vs branches with
          | Some (binds, l) ->
              let env' =
                List.fold_left (fun e (y, v) -> Env.add y v e) s.env binds
              in
              Next { label = l; env = env'; kont = s.kont }
          | None -> stuck "Match: no branch matches tag %s/%d" t (List.length vs)))

and find_fun (p : S_syntax.program) (f : S_syntax.var) :
    S_syntax.fundef option =
  List.find_opt (fun d -> String.equal d.S_syntax.name f) p.S_syntax.funs

(* No wildcard: a value whose tag matches no branch leaves the machine stuck. *)
and select_branch (t : S_syntax.tag) (vs : value list)
    (branches : (S_syntax.pat * Label.t) list) :
    ((S_syntax.var * value) list * Label.t) option =
  match branches with
  | [] -> None
  | (S_syntax.PTag (t', xs), l) :: rest ->
      if String.equal t t' && List.length xs = List.length vs then
        Some (List.combine xs vs, l)
      else select_branch t vs rest

and cmd_name (c : S_syntax.cmd) : string =
  match c with
  | S_syntax.Return _ -> "Return"
  | S_syntax.Let _ -> "Let"
  | S_syntax.LetCall _ -> "LetCall"
  | S_syntax.LetTag _ -> "LetTag"
  | S_syntax.Match _ -> "Match"

let inject ?(env = Env.empty) (p : S_syntax.program) : state =
  { label = p.S_syntax.main; env; kont = [] }

type outcome =
  | Final of value
  | OutOfFuel

let run ?(fuel = 1_000_000) ?(env = Env.empty) (p : S_syntax.program) : outcome =
  let rec loop n s =
    if n <= 0 then OutOfFuel
    else
      match step p s with
      | Done v -> Final v
      | Next s' -> loop (n - 1) s'
  in
  loop fuel (inject ~env p)

let run_value ?(fuel = 1_000_000) ?(env = Env.empty) (p : S_syntax.program) :
    value =
  match run ~fuel ~env p with
  | Final v -> v
  | OutOfFuel -> failwith "S_cek.run_value: step budget exhausted"

let rec string_of_value (v : value) : string =
  match v with
  | VInt n -> string_of_int n
  | VTag (t, []) -> t ^ "()"
  | VTag (t, vs) ->
      t ^ "(" ^ String.concat ", " (List.map string_of_value vs) ^ ")"
