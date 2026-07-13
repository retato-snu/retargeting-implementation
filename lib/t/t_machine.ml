(** The target language T's abstract machine, transcribed from the paper's
    langt-machine: the machine the retargeting construction derives from the
    S-coded definitional interpreter {!Interp_st}. It runs directly on the T
    abstract syntax of {!T_encoding} ([expr] / [value] / [env] / [defs]), with no
    detour through the S encoding. Two properties of the paper's machine drive
    its shape.

    {b Arithmetic, comparison and conditional frames carry no environment.} The
    right operand and the chosen branch are evaluated under the {e current}
    environment, which is sound by the machine's well-bracketedness: evaluating a
    subexpression always returns with the environment it started under restored.
    Only [Let] and [App], which genuinely change the environment, save and
    reinstate it, through an explicit [Restore] frame.

    {b The conditional return has an explicit [Silent] frame.} When [Ifz] selects
    a branch it pushes [Silent], and when the branch returns its value [T-Silent]
    pops it with no other effect. The frame stores nothing, but keeping it
    explicit rather than eliding it keeps the projection from the interpreter
    calculational.

    The implicit single parameter of every function is the variable id [0], the
    paper's [x_arg], matching the encoding and {!Interp_st}. *)

open T_encoding

(** {1 Continuation frames}

    The paper's frame set verbatim. For each operator, [Op1(e2)] holds the
    pending right operand while the left one is evaluated and [Op2(n1)] holds the
    evaluated left operand while the right one is; [Let] holds the bound variable
    and the body, [App] and the [App2_*]/[App3_*] family hold the callee id
    together with the operands still pending or already evaluated, [Ifz] holds the
    two branches, [Restore] holds the environment to reinstate, and [Silent] holds
    nothing. *)
type frame =
  | Add1 of expr  (** [Add1(e2)] — the pending right operand of an addition *)
  | Add2 of value  (** [Add2(n1)] — the evaluated left operand of an addition *)
  | Sub1 of expr  (** [Sub1(e2)] — the pending right operand of a subtraction *)
  | Sub2 of value  (** [Sub2(n1)] — the evaluated left operand of a subtraction *)
  | Mul1 of expr
  | Mul2 of value
  | Div1 of expr
  | Div2 of value
  | Mod1 of expr
  | Mod2 of value
  | Lt1 of expr
  | Lt2 of value
  | Let of var_id * expr  (** [Let(x, e2)] — bound variable and body *)
  | App of fun_id  (** [App(f)] — the argument of [f] is being evaluated *)
  | App2_1 of fun_id * expr
  | App2_2 of fun_id * value
  | App3_1 of fun_id * expr * expr
  | App3_2 of fun_id * value * expr
  | App3_3 of fun_id * value * value
  | Ifz of expr * expr  (** [Ifz(e2, e3)] — the then/else branches *)
  | Restore of env  (** [Restore(ρ)] — reinstate [ρ] on return (for [Let]/[App]) *)
  | Silent  (** [Silent()] — popped without effect when an [ifz] branch returns *)

(** A continuation: a stack of frames, innermost (most recently pushed) on top. *)
type kont = frame list

(** {1 Machine state}

    The control is either an expression still to evaluate or an integer value
    being returned to the continuation. *)
type control =
  | Expr of expr  (** an expression to evaluate *)
  | Value of value  (** a returned integer value *)

(** A T machine state [⟨q, ρ, κ⟩]: control, environment, continuation. *)
type state = { control : control; env : env; kont : kont }

(** {1 Errors} *)

(** Raised when the machine cannot make progress: an unbound variable, an
    undefined function, or any other shape the paper's rules do not cover. *)
exception Stuck of string

let stuck fmt = Printf.ksprintf (fun s -> raise (Stuck s)) fmt

(** {1 Environment and definition-table lookup}

    [env_lookup] reads the nearest binding of a variable in the encoding's
    association list; [fundef] reads a function's body from the program's
    definition table, the paper's decoded [D]. *)

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

(** {1 Transition} *)

(** Outcome of one machine step. *)
type step_result =
  | Next of state  (** the machine advanced to a new state *)
  | Done of value  (** the program returned a final value *)

(** One small-step of the T machine, parameterized by the program's definition
    table [defs] (the paper's [D]). With an {e expression} control the rule is
    chosen by the expression's form: an operator, a binder or a call pushes its
    frame and descends into its first subexpression ([T-Sub1], [T-Let1],
    [T-App1], [T-Ifz1], …), while [Int] and [Var] return immediately ([T-Int],
    [T-Var]). With a {e value} control the rule is chosen by the top frame, which
    either defers the next operand under the current environment, applies the
    operator, enters a body with a [Restore] frame, reinstates an environment, or
    takes an [ifz] branch. A value control with an empty continuation is the
    program's final result. The rules are named inline below. *)
let step (defs : defs) (s : state) : step_result =
  match s.control with
  | Expr e -> (
      match e with
      (* T-Int *)
      | Int (_, n) -> Next { s with control = Value n }
      (* T-Var *)
      | Var (_, x) -> Next { s with control = Value (env_lookup s.env x) }
      (* T-Add1 *)
      | Add (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Add1 e2 :: s.kont }
      (* T-Sub1 *)
      | Sub (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Sub1 e2 :: s.kont }
      (* T-Mul1 *)
      | Mul (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Mul1 e2 :: s.kont }
      (* T-Div1 / T-Mod1 / T-Lt1: as T-Sub1, evaluate the left operand first. *)
      | Div (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Div1 e2 :: s.kont }
      | Mod (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Mod1 e2 :: s.kont }
      | Lt (_, e1, e2) ->
          Next { s with control = Expr e1; kont = Lt1 e2 :: s.kont }
      (* T-Let1 *)
      | Let (_, x, e1, e2) ->
          Next { s with control = Expr e1; kont = Let (x, e2) :: s.kont }
      (* T-App1 *)
      | App (_, f, e1) ->
          Next { s with control = Expr e1; kont = App f :: s.kont }
      (* T-App2_1 / T-App3_1: evaluate the 1st operand, saving the callee and the
         operands still pending. As with the arithmetic frames these operand
         evaluations need no saved environment (well-bracketedness); only the
         call into the body pushes a [Restore]. *)
      | App2 (_, f, e1, e2) ->
          Next { s with control = Expr e1; kont = App2_1 (f, e2) :: s.kont }
      | App3 (_, f, e1, e2, e3) ->
          Next { s with control = Expr e1; kont = App3_1 (f, e2, e3) :: s.kont }
      (* T-Ifz1 *)
      | Ifz (_, e1, e2, e3) ->
          Next { s with control = Expr e1; kont = Ifz (e2, e3) :: s.kont })
  | Value n -> (
      match s.kont with
      | [] -> Done n
      (* T-Add2: left operand evaluated; defer the right operand under ρ. *)
      | Add1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Add2 n :: rest }
      (* T-Addr *)
      | Add2 n1 :: rest -> Next { s with control = Value (n1 + n); kont = rest }
      (* T-Sub2: as T-Add2. *)
      | Sub1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Sub2 n :: rest }
      (* T-Subr *)
      | Sub2 n1 :: rest -> Next { s with control = Value (n1 - n); kont = rest }
      (* T-Mul2 *)
      | Mul1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Mul2 n :: rest }
      (* T-Mulr *)
      | Mul2 n1 :: rest -> Next { s with control = Value (n1 * n); kont = rest }
      (* T-Div2 / T-Divr: the total quotient ([n1 / 0 = 0]), as in {!S_cek}. *)
      | Div1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Div2 n :: rest }
      | Div2 n1 :: rest ->
          Next { s with control = Value (if n = 0 then 0 else n1 / n); kont = rest }
      (* T-Mod2 / T-Modr: total remainder ([n1 mod 0 = 0]). *)
      | Mod1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Mod2 n :: rest }
      | Mod2 n1 :: rest ->
          Next
            { s with control = Value (if n = 0 then 0 else n1 mod n); kont = rest }
      (* T-Lt2 / T-Ltr: the integer [1] if [n1 < n] else [0]. *)
      | Lt1 e2 :: rest ->
          Next { s with control = Expr e2; kont = Lt2 n :: rest }
      | Lt2 n1 :: rest ->
          Next { s with control = Value (if n1 < n then 1 else 0); kont = rest }
      (* T-Let2: bind x in ρ, save ρ for restoration, evaluate the body. *)
      | Let (x, e2) :: rest ->
          Next
            {
              control = Expr e2;
              env = (x, n) :: s.env;
              kont = Restore s.env :: rest;
            }
      (* T-App2: enter D(f) with [x_arg ↦ n]; save caller ρ. *)
      | App f :: rest ->
          Next
            {
              control = Expr (fundef defs f);
              env = [ (x_arg, n) ];
              kont = Restore s.env :: rest;
            }
      (* T-App2_1r: 1st operand done; defer the 2nd under the current ρ. *)
      | App2_1 (f, e2) :: rest ->
          Next { s with control = Expr e2; kont = App2_2 (f, n) :: rest }
      (* T-App2_2r: both operands are values; enter D(f) with [[0↦n1; 1↦n2]],
         saving the caller's ρ. The binding order matches the interpreter's
         [extend(extend(Empty,0,v1),1,v2)] spine. *)
      | App2_2 (f, n1) :: rest ->
          Next
            {
              control = Expr (fundef defs f);
              env = [ (1, n); (0, n1) ];
              kont = Restore s.env :: rest;
            }
      (* T-App3_1r / T-App3_2r: thread the operands left to right. *)
      | App3_1 (f, e2, e3) :: rest ->
          Next { s with control = Expr e2; kont = App3_2 (f, n, e3) :: rest }
      | App3_2 (f, n1, e3) :: rest ->
          Next { s with control = Expr e3; kont = App3_3 (f, n1, n) :: rest }
      (* T-App3_3r: enter D(f) with [[0↦n1; 1↦n2; 2↦n3]], saving the caller's ρ. *)
      | App3_3 (f, n1, n2) :: rest ->
          Next
            {
              control = Expr (fundef defs f);
              env = [ (2, n); (1, n2); (0, n1) ];
              kont = Restore s.env :: rest;
            }
      (* T-Restore: reinstate the saved environment. *)
      | Restore env :: rest -> Next { control = Value n; env; kont = rest }
      (* T-Silent: pop with no other effect. *)
      | Silent :: rest -> Next { s with kont = rest }
      (* T-Ifz2 (n = 0) / T-Ifz3 (n ≠ 0): take a branch, push Silent. *)
      | Ifz (e2, e3) :: rest ->
          let branch = if n = 0 then e2 else e3 in
          Next { s with control = Expr branch; kont = Silent :: rest })

(** {1 Driver} *)

(** The initial state for [main] of [p] with top-level argument [arg]: control at
    the main expression, [x_arg] bound to [arg], and an empty continuation —
    mirroring the [main(p, arg)] seeding of {!Interp_st.eval_t}. *)
let inject ?(arg : value = 0) (p : program) : state =
  { control = Expr p.main; env = [ (x_arg, arg) ]; kont = [] }

(** Outcome of running a program. *)
type outcome =
  | Final of value  (** the program reached a final value *)
  | OutOfFuel  (** the step guard tripped before a final value was reached *)

(** Run [p] from its initial state to a final value, taking at most [fuel] steps
    so a non-terminating program cannot loop forever. A stuck state raises
    {!Stuck}. *)
let run_outcome ?(fuel = 1_000_000) ?(arg : value = 0) (p : program) : outcome =
  let rec loop n s =
    if n <= 0 then OutOfFuel
    else
      match step p.defs s with
      | Done v -> Final v
      | Next s' -> loop (n - 1) s'
  in
  loop fuel (inject ~arg p)

(** Run a T program and return its final value. [arg] is the top-level argument
    bound to the implicit parameter (default [0]), the convention of
    {!Interp_st.eval_t}, so the two drivers are directly comparable. Raises
    {!Stuck} on a stuck state and [Failure] on an exhausted step budget. *)
let run ?(fuel = 1_000_000) ?(arg : value = 0) (p : program) : value =
  match run_outcome ~fuel ~arg p with
  | Final v -> v
  | OutOfFuel -> failwith "T_machine.run: step budget exhausted"
