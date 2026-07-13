(** Concrete S CEK machine: the executable reference semantics for the S core
    language, and the concrete oracle on top of which the abstract S interpreter
    is later built.

    It is a C_aEK machine: because core S is in (relaxed) A-normal form, the
    control component is a label naming a command rather than an arbitrary
    expression, and only function calls transfer control. A state is a triple
    [(label, environment, continuation)], a continuation is a list of frames,
    each recording a suspended command label with the environment to restore when
    the call it suspends returns, and values are integers and tagged tuples. The
    transition relation covers the four command forms [Return], [Let], [LetCall]
    and [Match], plus the expression evaluator [eval_exp]. *)

(** {1 Values} *)

type value =
  | VInt of int
  | VTag of S_syntax.tag * value list

(** {1 Environment} *)

module Env = Map.Make (String)

type env = value Env.t

(** {1 Continuation} *)

(** The paper's frame: the pair [(suspended label, saved env)]. The suspended
    command is always the [LetCall] that pushed the frame; its [var]/[label]
    fields say where the returned value is bound and where control resumes. *)
type frame = { suspended : Label.t; saved_env : env }

(** A stack of frames, innermost call on top. *)
type kont = frame list

(** {1 Machine state} *)

type state = { label : Label.t; env : env; kont : kont }

(** {1 Errors} *)

(** Raised when the machine cannot make progress: an unbound variable, a
    primitive misuse, a malformed frame, a non-exhaustive match. *)
exception Stuck of string

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck s)) fmt

(** {1 Variable lookup} *)

let lookup (rho : env) (x : S_syntax.var) : value =
  match Env.find_opt x rho with
  | Some v -> v
  | None -> stuck "unbound variable %s" x

(** {1 Primitives} *)

(** Interpretation of a primitive operator on argument values: the paper's binary
    integer arithmetic [add], [sub] and [mul], the total [div] / [mod] / [lt],
    and the two tests [eq] ([a == b]) and [iszero], which yield a Boolean as a
    nullary constructor — [True()] when the test holds, [False()] otherwise. *)
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
  let bool_of b = if b then VTag ("True", []) else VTag ("False", []) in
  match o with
  | "add" -> bin "add" ( + )
  | "sub" -> bin "sub" ( - )
  | "mul" -> bin "mul" ( * )
  (* OCaml's [/] truncates toward zero and its [mod] takes the sign of the
     dividend, so for [b <> 0] they realise the intended quotient and
     [a - b*(a/b)]. Division and remainder by zero are defined to be [0] rather
     than raising, keeping the interpreter total: [div(_,0) = mod(_,0) = 0]. *)
  | "div" -> bin "div" (fun a b -> if b = 0 then 0 else a / b)
  | "mod" -> bin "mod" (fun a b -> if b = 0 then 0 else a mod b)
  | "lt" -> bin "lt" (fun a b -> if a < b then 1 else 0)
  | "eq" -> (
      match args with
      | [ a; b ] -> bool_of (as_int "eq" 0 a = as_int "eq" 1 b)
      | _ ->
          stuck "primitive eq: expected 2 arguments, got %d" (List.length args))
  | "iszero" -> (
      match args with
      | [ a ] -> bool_of (as_int "iszero" 0 a = 0)
      | _ ->
          stuck "primitive iszero: expected 1 argument, got %d"
            (List.length args))
  | _ -> stuck "unknown primitive %s" o

(** {1 Expression evaluation} *)

(** Evaluate an expression in an environment (the paper's [eval e ρ]): an integer
    literal, a variable, or a primitive/constructor application whose operands
    are themselves evaluated recursively (relaxed ANF). Evaluation transfers no
    control and fails only on an unbound variable or a primitive misuse. *)
let rec eval_exp (e : S_syntax.exp) (rho : env) : value =
  match e with
  | S_syntax.EInt n -> VInt n
  | S_syntax.EVar x -> lookup rho x
  | S_syntax.EPrim (o, es) -> eval_prim o (List.map (fun e -> eval_exp e rho) es)
  | S_syntax.ETag (_site, t, es) -> VTag (t, List.map (fun e -> eval_exp e rho) es)

(** {1 Transition} *)

(** Outcome of one machine step. *)
type step_result =
  | Next of state  (** the machine advanced to a new state *)
  | Done of value  (** the program returned a final value *)

(** One small-step of the S-CEK machine; the command at the current label picks
    the rule.

    - [Return e] — evaluate [e]. With a frame [(suspended, saved_env)] on top,
      pop it, bind the suspended [LetCall]'s result variable to the value in
      [saved_env] and resume at that call's body label (rule [S-Return]); with an
      empty continuation, [e]'s value is the program's result.
    - [Let (x, e, l)] — bind [x] to [eval_exp e] and continue at [l] (rule
      [S-LetExp]); a constructor allocation is an [ETag] right-hand side and is
      handled here.
    - [LetCall (x, f, args, l)] — evaluate the arguments, build the callee's
      environment from its formals, push the frame [(current label, current env)]
      and jump to the callee's entry (rule [S-LetCall]). The suspended label is
      the [LetCall] itself, so [S-Return] can recover [x] and [l].
    - [Match (e, branches)] — evaluate the scrutinee to a tagged value [T(v...)],
      take the first branch whose pattern matches [T] at the same arity, bind its
      variables and continue at its label (rule [S-Match]); no matching branch is
      stuck. *)
let rec step (p : S_syntax.program) (s : state) : step_result =
  match S_syntax.cmd_at p s.label with
  | S_syntax.Return a -> (
      let v = eval_exp a s.env in
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
  | S_syntax.Let (x, e, l) ->
      let v = eval_exp e s.env in
      Next { label = l; env = Env.add x v s.env; kont = s.kont }
  | S_syntax.LetCall (_x, f, args, _l) -> (
      (* [_x] and [_l] are recovered later by S-Return from the suspended label,
         so they are not consumed at call time. *)
      match find_fun p f with
      | None -> stuck "LetCall: undefined function %s" f
      | Some def ->
          let arg_vals = List.map (fun a -> eval_exp a s.env) args in
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
  | S_syntax.Match (a, branches) -> (
      match eval_exp a s.env with
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

(** Select the first branch whose [PTag] agrees with the scrutinee's tag and
    arity, returning its bindings and continuation label. There is no wildcard,
    so a value matching no branch leaves the machine stuck. *)
and select_branch (t : S_syntax.tag) (vs : value list)
    (branches : (S_syntax.pat * Label.t) list) :
    ((S_syntax.var * value) list * Label.t) option =
  match branches with
  | [] -> None
  | (S_syntax.PTag (t', xs), l) :: rest ->
      if String.equal t t' && List.length xs = List.length vs then
        Some (List.combine xs vs, l)
      else select_branch t vs rest

(* A command form's name, for error messages. *)
and cmd_name (c : S_syntax.cmd) : string =
  match c with
  | S_syntax.Return _ -> "Return"
  | S_syntax.Let _ -> "Let"
  | S_syntax.LetCall _ -> "LetCall"
  | S_syntax.Match _ -> "Match"

(** {1 Driver} *)

(** The initial state: control at [main], an empty continuation, and an
    environment seeded by the optional [env] (externally supplied bindings). *)
let inject ?(env = Env.empty) (p : S_syntax.program) : state =
  { label = p.S_syntax.main; env; kont = [] }

(** Outcome of running a program. *)
type outcome =
  | Final of value  (** the program reached a final value *)
  | OutOfFuel  (** the step guard tripped before a final value was reached *)

(** Run a program from [main] to a final value. [fuel] bounds the number of steps
    so a non-terminating program cannot loop forever; a stuck state raises
    {!Stuck}. *)
let run ?(fuel = 1_000_000) ?(env = Env.empty) (p : S_syntax.program) : outcome =
  let rec loop n s =
    if n <= 0 then OutOfFuel
    else
      match step p s with
      | Done v -> Final v
      | Next s' -> loop (n - 1) s'
  in
  loop fuel (inject ~env p)

(** {!run}, returning the final value; raises {!Stuck} if the program gets stuck
    and [Failure] if it exhausts its step budget. *)
let run_value ?(fuel = 1_000_000) ?(env = Env.empty) (p : S_syntax.program) :
    value =
  match run ~fuel ~env p with
  | Final v -> v
  | OutOfFuel -> failwith "S_cek.run_value: step budget exhausted"

(** {1 Pretty-printing} *)

(** Render a value as a string, e.g. [42], [Cons(1, Nil())]. *)
let rec string_of_value (v : value) : string =
  match v with
  | VInt n -> string_of_int n
  | VTag (t, []) -> t ^ "()"
  | VTag (t, vs) ->
      t ^ "(" ^ String.concat ", " (List.map string_of_value vs) ^ ")"
