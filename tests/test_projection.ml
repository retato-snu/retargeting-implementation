(* The concrete S -> T projection / macro-step bisimulation (Projection), plus
   the differential cross-check tying the two evaluators together.

   Running I_S^T on the concrete S machine and observing it at interpreter points
   projects to a valid trace of the paper's T machine. The differential check
   first establishes that the direct T machine and the S-coded interpreter agree
   on every program (and argument); the projection checks then verify that the
   projected trace is a valid — indeed identical — T-machine run. *)

open Retargeting
open Test_util

let run () =
  (* Differential cross-check: the paper's direct T-machine and the S-coded
     interpreter I_S^T must agree on every program (and argument). This is the
     oracle check tying the two evaluators together. *)
  List.iter
    (fun (name, p) ->
      List.iter
        (fun arg ->
          check
            (Printf.sprintf "differential %s (arg=%d): tmachine = interp" name
               arg)
            (T_machine.run ~arg p = Interp_st.eval_t ~arg p))
        [ 0; 1; 5; -2 ])
    diff_programs;

  (* The interpreter points are extracted structurally, matching the paper's
     L_call and L_ret. The listing itself has 9 ret (int/var/add/sub/mul/let/app/
     ifz2/ifz3) and 13 call (two per binary operator, let1/let2, app1/app2, and
     ifz1/ifz2/ifz3). The extension's Div/Mod/Lt branches add 3 ret and 3*2 = 6
     call (→ 12 ret / 19 call); its multi-arg App branches add one eval-return
     each (→ 14 ret) and their operand+body eval-calls: App2 has 2 operand + 1
     body = 3, App3 has 3 operand + 1 body = 4 (→ 19+3+4 = 26 call). *)
  check "projection: 14 eval-return labels extracted"
    (List.length Projection.points.Projection.Points.ret_labels = 14);
  check "projection: 26 eval-call labels extracted"
    (List.length Projection.points.Projection.Points.call_frames = 26);

  (* For each T program (and argument), the projected trace must be a valid
     T-machine run: consecutive decoded states are T_machine.step-connected. The
     strongest oracle is that the projected trace equals the T machine's own
     state sequence for the same program. *)
  let projection_valid name p arg =
    check
      (Printf.sprintf "projection valid: %s (arg=%d)" name arg)
      (match Projection.verify_program ~arg p with
      | Projection.Valid -> true
      | Projection.Empty -> false
      | Projection.Mismatch _ -> false);
    check
      (Printf.sprintf "projection = T-machine trace: %s (arg=%d)" name arg)
      (Projection.equals_t_machine ~arg p)
  in
  List.iter
    (fun (name, p) ->
      List.iter (fun arg -> projection_valid name p arg) [ 0; 1; 5; -2 ])
    diff_programs;

  (* Multi-argument application (App2 / App3) — the operand-eval frames and the
     multi-binding callee environment must project to the langt-machine
     exactly as App1 does. Each program is cross-checked both ways: the direct
     T-machine equals the S-coded interpreter, and the projected trace IS the
     T-machine trace. These are closed programs (the main is a call), so the
     argument is immaterial; a spread is still run. *)
  let multiarg_programs =
    [
      ("add via App2", parse_t "add(x, y) = x - (0 - y); add(3, 4)");
      ("gcd via App2 + mod",
       parse_t "g(a, b) = ifz b then a else g(b, a % b); g(48, 36)");
      ("tak via App3 + lt",
       parse_t
         "tak(x, y, z) = ifz (y < x) then tak(tak(x - 1, y, z), tak(y - 1, z, \
          x), tak(z - 1, x, y)) else z; tak(4, 2, 0)");
      ("ackermann via App2",
       parse_t
         "a(m, n) = ifz m then n - (0 - 1) else ifz n then a(m - 1, 1) else a(m \
          - 1, a(m, n - 1)); a(2, 2)");
      (* a [let] inside a 2-ary body: the let-bound id must not collide with the
         second parameter's id (1). If it did, [b] would be shadowed and the
         result would be wrong — the value assertions below pin it. *)
      ("let inside App2 body",
       parse_t "f(a, b) = let c = a - b in c * b; f(5, 3)");
    ]
  in
  (* Concrete-value oracles (the interpreter is the ground truth): these pin the
     witness results the brief specifies and, for the let-body case, the param/
     let id disambiguation. *)
  List.iter
    (fun (src, expected) ->
      check
        (Printf.sprintf "multi-arg value: %s = %d" src expected)
        (Interp_st.eval_t (parse_t src) = expected))
    [
      ("add(x, y) = x - (0 - y); add(3, 4)", 7);
      ("g(a, b) = ifz b then a else g(b, a % b); g(48, 36)", 12);
      ("g(a, b) = ifz b then a else g(b, a % b); g(48, 30)", 6);
      ("a(m, n) = ifz m then n - (0 - 1) else ifz n then a(m - 1, 1) else a(m - \
        1, a(m, n - 1)); a(2, 2)", 7);
      ("f(a, b) = let c = a - b in c * b; f(5, 3)", 6);
      (* a 3-ary body with two lets, exercising ids 0/1/2 (params) then 3/4:
         u = 2-(0-3) = 5, v = 5-1 = 4, v*a = 8. *)
      ("h(a, b, c) = let u = a - (0 - b) in let v = u - c in v * a; h(2, 3, 1)",
       8);
    ];
  List.iter
    (fun (name, p) ->
      List.iter
        (fun arg ->
          check
            (Printf.sprintf "differential %s (arg=%d): tmachine = interp" name arg)
            (T_machine.run ~arg p = Interp_st.eval_t ~arg p);
          projection_valid name p arg)
        [ 0; 1; 5; -2 ])
    multiarg_programs;

  (* The first projected state is the T machine's initial state, and the last is
     a returned value with an empty continuation (the program's result). *)
  let arith = parse_t "(3 - 1) * 2" in
  let pr = Projection.project arith in
  check "projection: first state is the T initial state"
    (match pr.Projection.states with
    | first :: _ -> first = T_machine.inject arith
    | [] -> false);
  (* The final control [Value 4] is the program's computed result (4), not a
     label, so it stays a literal; the continuation is empty at termination. *)
  check "projection: last state is a value with empty continuation"
    (match List.rev pr.Projection.states with
    | { T_machine.control = T_machine.Value 4; kont = []; _ } :: _ -> true
    | _ -> false);

  (* Negative check: a projected trace with a state dropped must be reported as a
     Mismatch, so verification genuinely tests the T step relation. *)
  check "projection: a corrupted trace is rejected"
    (let corrupted =
       {
         pr with
         Projection.states =
           (match pr.Projection.states with
           | a :: _ :: rest -> a :: rest
           | other -> other);
       }
     in
     match Projection.verify corrupted with
     | Projection.Mismatch _ -> true
     | Projection.Valid | Projection.Empty -> false);

  banner "all projection tests passed"
