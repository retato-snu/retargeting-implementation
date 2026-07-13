(** Generic abstract interpreter for the S core language: a sound, terminating
    abstract machine mirroring the concrete S-CEK machine {!S_cek} over abstract
    values, keyed by the retargeting frame index {!Partition} and parameterized
    over the value domain. Run on the S-coded T interpreter {!Interp_st}
    ([I_S^T]) it is the base analyzer of the paper, computing a T-sensitive
    over-approximation of every T program the interpreter can run.

    The abstract state [σ̂ : State ::= [π̂ ↦ ⟨ρ̂, κ̂-set⟩]] is a finite table keyed by
    a part [π̂ = ⟨φ̂, κ̂⟩]: the frame index [φ̂] ({!Partition.t}, label-respecting
    through {!Partition.lab}) carries the T-view sensitivity, and the continuation
    index [κ̂ ∈ Kont̂ = {•} ∪ ℘(Lab_P)] ({!kidx}) keys returns by the pending
    T-expression's labels. The payload pairs the environment [ρ̂] with the stored
    continuation set [κ̂-set] ({!kont}), whose elements are [•] or a caller part
    [⟨φ̂_c, κ̂_c⟩] carrying the caller's {b real} continuation index — so [AbsReturn]
    reads the caller entry by a {e precise} key lookup, with no truncation, no
    superset resume and no [push⁻¹] table. The local rules [AbsLetExp],
    [AbsLetCall], [AbsReturn], [AbsMatch] act directly on the table with the
    write-back refinement [ρ̂' ⊓ env(φ̂')] folded in, the retargeted [pusĥ] ({!push})
    is computed forward at a call, and the analysis is the least fixpoint of the
    join of the view-indexed steps ({!solve}).

    {b Termination.} S labels are finite and T-label sets are drawn from the
    program's finitely many T labels, so table keys are finite; each entry's
    environment lives in the value domain, whose ascending chains stabilize under
    {!D.widen}, and {!solve} widens revisited entries at the reentrant points. *)
module Make (D : Domain_intf.DOMAIN) = struct
module Env = Map.Make (String)

(** An abstract environment [ρ̂]: S variables to abstract values. Following the
    paper it is a total map — an absent variable reads as {!D.bottom} — and it is
    {e bottom-strict}: {!aenv_add} drops a bottom binding rather than storing it,
    so a bound variable is never bound to bottom. *)
type aenv = D.t Env.t

let aenv_empty : aenv = Env.empty

let aenv_find (rho : aenv) (x : S_syntax.var) : D.t =
  match Env.find_opt x rho with Some v -> v | None -> D.bottom

let aenv_add (x : S_syntax.var) (v : D.t) (rho : aenv) : aenv =
  if D.is_bottom v then Env.remove x rho else Env.add x v rho

let aenv_join (a : aenv) (b : aenv) : aenv =
  Env.merge
    (fun _ va vb ->
      match (va, vb) with
      | None, None -> None
      | Some v, None | None, Some v -> Some v
      | Some v1, Some v2 -> Some (D.join v1 v2))
    a b

let aenv_widen (a : aenv) (b : aenv) : aenv =
  Env.merge
    (fun _ va vb ->
      match (va, vb) with
      | None, None -> None
      | Some v, None | None, Some v -> Some v
      | Some v1, Some v2 -> Some (D.widen v1 v2))
    a b

(** Pointwise order: [a <= b] iff every binding of [a] is below [b]'s (with
    missing bindings read as bottom). Physical equality of the two values is a
    fast path ([v ⊑ v] always holds), which pays off on the large,
    structurally-shared input value threaded unchanged through the analysis.

    {b Why this still terminates.} {!update} treats [not (aenv_leq rho old)] as
    "grew", so repeated growth flags on γ-equal values would loop the worklist.
    They cannot — but {e not} by the paper's order-embedding, which presupposes that
    symbols partition the concrete trees: the allocation-site instantiation of [Sym]
    violates that premise (the interpreter's glue [Var(l0,x0)] and an encoded input
    [Var] node both concretize [Var(0,0)]), so structural [D.leq] is sound (⊑ ⇒ γ ⊆)
    but not complete. The grounds are representational instead: on every growth the
    stored value becomes [widen old (join old new)], which structurally strictly
    increases, and the representation lattice has no infinite ascending chains
    (finitely many site × tag symbols of fixed arity; the graded [aint] saturates
    past [fin_widen_bound]). An incomplete [leq] can at worst store a γ-redundant
    representation once; it cannot re-flag an unchanged value, whose recomputed
    successor is structurally identical and already subsumed. *)
let aenv_leq (a : aenv) (b : aenv) : bool =
  Env.for_all
    (fun x v ->
      let bv = aenv_find b x in
      v == bv || D.leq v bv)
    a

(** {1 The continuation partition index and the stored continuation set}

    The paper's [Kont̂ = {•} ∪ Lab_P] (§impl-t-flow) is represented here in the
    set-valued form [{•} ∪ ℘(Lab_P)] — a sound coarsening that stays total under
    joins; the exact single-label form is what the disambiguated value domain
    adds. *)

(** The continuation partition index [κ̂]: the empty-continuation context [•], or
    the T-labels of the pending T-expressions a return resumes into. *)
type kidx = KBullet | KTLabs of Label.Set.t

let compare_kidx (a : kidx) (b : kidx) : int =
  match (a, b) with
  | KBullet, KBullet -> 0
  | KBullet, KTLabs _ -> -1
  | KTLabs _, KBullet -> 1
  | KTLabs s1, KTLabs s2 -> Label.Set.compare s1 s2

(** A caller part [π̂ = ⟨φ̂_c, κ̂_c⟩]: a frame index with its {e real} continuation
    index, not a truncated placeholder, so a return looks the caller up exactly. *)
type part = { pphi : Partition.t; pkont : kidx }

type kelem = KEmpty | KPart of part

(** A stored continuation set [κ̂-set]: sorted and deduplicated. *)
type kont = kelem list

let compare_part (p : part) (q : part) : int =
  let c = Partition.compare p.pphi q.pphi in
  if c <> 0 then c else compare_kidx p.pkont q.pkont

let compare_kelem (a : kelem) (b : kelem) : int =
  match (a, b) with
  | KEmpty, KEmpty -> 0
  | KEmpty, KPart _ -> -1
  | KPart _, KEmpty -> 1
  | KPart p, KPart q -> compare_part p q

let compare_kont (a : kont) (b : kont) : int =
  List.compare compare_kelem a b

(** [{•}] — the continuation of the program's top-level frame. *)
let kont_halt : kont = [ KEmpty ]

let rec kont_insert (e : kelem) (k : kont) : kont =
  match k with
  | [] -> [ e ]
  | x :: rest ->
      let c = compare_kelem e x in
      if c < 0 then e :: k else if c = 0 then k else x :: kont_insert e rest

let kont_union (a : kont) (b : kont) : kont = List.fold_left (fun acc e -> kont_insert e acc) b a

(** Is the kont-set empty (no [•] and no caller part)? By bottom-strictness a
    bound state entry must have a non-empty continuation. *)
let kont_is_empty (k : kont) : bool = k = []

let string_of_kelem_short (e : kelem) : string =
  match e with
  | KEmpty -> "*"
  | KPart p -> "k" ^ Partition.to_string p.pphi

let string_of_kont (k : kont) : string =
  "{" ^ String.concat "," (List.map string_of_kelem_short k) ^ "}"

(** {1 Abstract state: the tabulated entries} *)

(** A table key is an abstract part [π̂ = ⟨φ̂, κ̂⟩]. *)
module Key = struct
  type t = Partition.t * kidx

  let compare ((p1, k1) : t) ((p2, k2) : t) : int =
    let c = Partition.compare p1 p2 in
    if c <> 0 then c else compare_kidx k1 k2
end

module Table = Map.Make (Key)

(** The abstract state [σ̂]: a finite map from parts to [⟨ρ̂, κ̂-set⟩]. *)
type entry = { rho : aenv; kont : kont }
type state = entry Table.t

let state_empty : state = Table.empty

(** Read the entry at a key. A missing key reads as bottom: empty environment,
    empty continuation set. *)
let table_find (sigma : state) (key : Key.t) : entry =
  match Table.find_opt key sigma with
  | Some e -> e
  | None -> { rho = aenv_empty; kont = [] }

let part_of_key ((phi, k) : Key.t) : part = { pphi = phi; pkont = k }

module KeySet = Set.Make (Key)

(** {1 Dependency index: an incremental reverse view of the table}

    [AbsReturn] looks the caller entry up by a precise key, so no forward index is
    needed; the worklist's reverse edge ({!dependents}) does need one, since when a
    caller entry grows every [Return] naming that caller part must be re-processed.
    The index is an exact, incrementally maintained view of the table, so it only
    changes how those returns are {e found}: the set found, hence the fixpoint,
    equals that of the table scan {!dependents} falls back to without it. *)

module KeyMap = Map.Make (Key)

(** The caller parts a stored continuation set names, as table keys. *)
let kont_mentioned_parts (k : kont) : Key.t list =
  List.filter_map
    (fun (e : kelem) ->
      match e with KEmpty -> None | KPart p -> Some (p.pphi, p.pkont))
    k

(** An incremental reverse index over a table: [rev ⟨φ̂_c,κ̂_c⟩] is the set of
    [Return] keys whose stored continuation names the caller part [⟨φ̂_c,κ̂_c⟩].
    [is_return φ̂] caches whether the command at [φ̂] is a [Return]. *)
type index = {
  mutable rev : KeySet.t KeyMap.t;
  is_return : Partition.t -> bool;
}

let keymap_find_set (m : KeySet.t KeyMap.t) (k : Key.t) : KeySet.t =
  match KeyMap.find_opt k m with Some s -> s | None -> KeySet.empty

(** Record that key [key] now stores continuation [new_kont] ([old_kont] is [\[\]]
    for a brand-new key): add [key] to the reverse index of every caller part the
    continuation has newly come to mention. A no-op unless [key] is a [Return]. *)
let idx_record (idx : index) (key : Key.t) ~(old_kont : kont) ~(new_kont : kont) :
    unit =
  if idx.is_return (fst key) then begin
    let old_mentions = kont_mentioned_parts old_kont in
    let newly =
      List.filter
        (fun cpk ->
          not (List.exists (fun q -> Key.compare cpk q = 0) old_mentions))
        (kont_mentioned_parts new_kont)
    in
    List.iter
      (fun cpk ->
        idx.rev <-
          KeyMap.add cpk (KeySet.add key (keymap_find_set idx.rev cpk)) idx.rev)
      newly
  end

(** Build a fresh index reflecting the whole table, to seed a [solve]. *)
let index_of_state (is_return : Partition.t -> bool) (sigma : state) : index =
  let idx = { rev = KeyMap.empty; is_return } in
  Table.iter
    (fun key (e : entry) -> idx_record idx key ~old_kont:[] ~new_kont:e.kont)
    sigma;
  idx

(** {1 The program under analysis and its derived data}

    A handle bundles the S program with the read-only facts the abstract step
    needs, all obtained from the same structural extraction the concrete
    projection uses, so nothing is hardcoded.

    {2 Optional auxiliary folding}

    By default the base discharges an auxiliary call ([lookup]/[fundef]/[extend])
    like any other [LetCall], stepping the helper body through the shared table (the
    global [summ_aux], the paper's [Fixaux] summary). A driver may instead supply an
    {!aux_config} to fold the family: the callee entry is bypassed and the call
    discharged by a [def:auxop] transfer operator — the closed-form mode of
    def:absmacrofull, a separately-more-precise construction (⊑ the summary base). *)

type aux_op =
  | Closed of (S_syntax.var -> D.t list -> D.t option)
      (** a pure [def:auxop] transfer, applied to the aux name and argument
          values: the domain closed form ([Domain_rtg.aux_denot] /
          [Domain_dis.aux_denot] — the paper's [A⟦h⟧], lem:auxdenote) *)
  | Delimited
      (** discharge the call by a delimited base fixpoint of the callee body
          read back at [•], memoized in [aux_memo] *)

type aux_config = {
  aux_names : string list;  (** the certified auxiliary family [Ω] to fold *)
  aux_op : aux_op;
  aux_memo : (S_syntax.var * kidx * D.t list, D.t option) Hashtbl.t;
      (** the [Delimited] summary memo (unused by [Closed]); fresh per run *)
}

(** A [Closed] folding config over a pure transfer [denot]. *)
let aux_closed (aux_names : string list)
    (denot : S_syntax.var -> D.t list -> D.t option) : aux_config =
  { aux_names; aux_op = Closed denot; aux_memo = Hashtbl.create 1 }

(** A [Delimited] folding config: each aux call is discharged by a delimited,
    memoized base fixpoint of the callee body. *)
let aux_delimited (aux_names : string list) : aux_config =
  { aux_names; aux_op = Delimited; aux_memo = Hashtbl.create 64 }

type handle = {
  prog : S_syntax.program;
  eval_entry : Label.t;
  eval_e : S_syntax.var;
  eval_call_labels : Label.Set.t;
  eval_body : Label.Set.t;
      (** the labels of [eval]'s own body (the paper's [Lab_eval]), used by the
          retargeted [pusĥ]'s call-site case analysis *)
  in_scope : S_syntax.var list Label.Map.t;
      (** the variables that may be in scope at each S label, used by the
          [env : Frame → Env] map of the indexed write-back *)
  exact_pins : D.t Label.Map.t option;
      (** [Some pins] switches on the designated instance (§impl-t-flow, see
          {!partitions_of}); [None] (the default) keeps the set-valued
          no-disambiguation mode, where frames carry the whole label {e set} and the
          environment is only scope-restricted. *)
  aux : aux_config option;
      (** [Some cfg] switches on auxiliary folding; [None] keeps the summary base. *)
  widen_pts : Label.Set.t;
      (** The labels at which {!solve} widens a revisited entry, joining at every
          other label. See {!reentrant_points}. *)
}

(** Forward reference to the delimited summary (definable only once {!solve} and
    {!read_result} exist), breaking the [step_entry ↔ solve] cycle that the
    [Delimited] auxiliary operator introduces. *)
let delimited_hook :
    (handle -> aux_config -> kidx -> S_syntax.fundef -> D.t list -> D.t option)
    ref =
  ref (fun _ _ _ _ _ -> None)

(** The intra-procedural label set of the body entered at [entry]: the labels
    reachable through continuation edges only, never through a call into a callee
    body. This realizes the paper's [Lab_eval]. A scope-based test ("[e] in scope
    here") is {b not} a correct realization: [main]'s glue binds its own variable
    named [e], so that test would classify [main]'s auxiliary calls as eval-body
    calls and merge them with genuine eval-issued auxiliary runs at the same
    T-label. *)
let fun_body_labels (prog : S_syntax.program) (entry : Label.t) : Label.Set.t =
  let rec go (seen : Label.Set.t) (l : Label.t) : Label.Set.t =
    if Label.Set.mem l seen then seen
    else
      let seen = Label.Set.add l seen in
      match S_syntax.cmd_at prog l with
      | S_syntax.Return _ -> seen
      | S_syntax.Let (_, _, k) -> go seen k
      | S_syntax.LetCall (_, _, _, k) -> go seen k
      | S_syntax.Match (_, branches) ->
          List.fold_left (fun s (_, k) -> go s k) seen branches
  in
  go Label.Set.empty entry

(** {2 The in-scope variable analysis (the [env] map's support)}

    A forward "may be bound" dataflow over the S control map: a variable may be in
    scope at a label if some path from a function entry binds it before reaching
    that label; a function entry starts with exactly its formals bound. This is
    the support of the paper's [env : Frame → Env] map (see {!env_of_frame}). *)
let compute_in_scope (prog : S_syntax.program)
    (seed_vars : (Label.t * S_syntax.var list) list) :
    S_syntax.var list Label.Map.t =
  let module SS = Set.Make (String) in
  (* A function's entry starts with its formals bound, plus any extra seeds (e.g.
     [main]'s externally-supplied variables). The seeds keep the may-be-bound
     scope an over-approximation that never drops a live variable, which the
     [⊓ env] refinement needs to be sound. *)
  let entry_bound : SS.t Label.Map.t =
    List.fold_left
      (fun acc (d : S_syntax.fundef) ->
        Label.Map.add d.S_syntax.entry (SS.of_list d.S_syntax.params) acc)
      Label.Map.empty prog.S_syntax.funs
  in
  let entry_bound =
    List.fold_left
      (fun acc (l, vs) ->
        let old = match Label.Map.find_opt l acc with Some s -> s | None -> SS.empty in
        Label.Map.add l (SS.union old (SS.of_list vs)) acc)
      entry_bound seed_vars
  in
  let succ_bound (l : Label.t) (bound : SS.t) : (Label.t * SS.t) list =
    match S_syntax.cmd_at prog l with
    | S_syntax.Return _ -> []
    | S_syntax.Let (x, _, k) -> [ (k, SS.add x bound) ]
    | S_syntax.LetCall (_, _, _, _) ->
        (* The callee entry is seeded separately (its formals); the continuation
           edge, which also binds the result variable, comes from [call_succ]. *)
        []
    | S_syntax.Match (_, branches) ->
        List.map
          (fun (S_syntax.PTag (_, vars), k) ->
            (k, List.fold_left (fun s v -> SS.add v s) bound vars))
          branches
  in
  (* LetCall continuations: the result variable is bound at the continuation. *)
  let call_succ (l : Label.t) (bound : SS.t) : (Label.t * SS.t) list =
    match S_syntax.cmd_at prog l with
    | S_syntax.LetCall (x, _, _, k) -> [ (k, SS.add x bound) ]
    | _ -> []
  in
  let table = ref entry_bound in
  let get l = match Label.Map.find_opt l !table with Some s -> s | None -> SS.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    Label.Map.iter
      (fun l _cmd ->
        let bound = get l in
        let succs = succ_bound l bound @ call_succ l bound in
        List.iter
          (fun (k, s) ->
            let old = get k in
            let merged = SS.union old s in
            if not (SS.equal merged old) then (
              table := Label.Map.add k merged !table;
              changed := true))
          succs)
      prog.S_syntax.ctrl
  done;
  Label.Map.map SS.elements !table

let in_scope_at (h : handle) (l : Label.t) : S_syntax.var list =
  match Label.Map.find_opt l h.in_scope with Some vs -> vs | None -> []

(** The paper's [env : Frame → Env] map, represented by its support: the variables
    in scope at [lab(φ̂)]. The environment it stands for maps each in-scope
    variable to top and is undefined elsewhere, so [γ_Env(env(φ̂))] is exactly the
    set of environments whose domain is contained in the in-scope variables — the
    requirement [{ρ | ⟨ℓ,ρ⟩ ∈ δ_Frame(φ̂)} = γ_Env(env(φ̂))]. *)
let env_of_frame (h : handle) (phi : Partition.t) : string list =
  in_scope_at h (Partition.lab phi)

(** The write-back's [ρ̂' ⊓ env(φ̂')]: a domain restriction, since an in-scope
    variable keeps its value ([v ⊓ ⊤ = v]) and an out-of-scope one is dropped. *)
let aenv_meet_scope (rho : aenv) (scope : string list) : aenv =
  let module SS = Set.Make (String) in
  let keep = SS.of_list scope in
  Env.filter (fun x _ -> SS.mem x keep) rho

(** The {b reentrant points} of an S program: the labels at which the fixpoint
    must widen to terminate, computed from the program text alone.

    In the (relaxed-ANF, first-order) core S a function body's own control flow is
    acyclic — [Let]/[LetCall]/[Match] fall through, [Return] ends the body, and there
    is no loop form — so every cycle in the analysis's dependency graph comes from
    recursion: a call re-enters a body at its entry and the value flows back out
    through that body's [Return] to the caller's frame. The procedure boundaries
    (function entries including [main]'s, [Return] commands, [LetCall] sites)
    therefore cut every cycle, and the straight-line interior of a body is acyclic
    and can be joined.

    Joining at the interior is not merely an optimization: it is what makes the
    specialization {e exact}. The specialized analyzer tabulates exactly these
    boundaries (it composes the interior transfers away), so widening at interior
    labels too would widen at points the specialized analyzer does not have, and the
    two fixpoints would differ — the base coming out strictly coarser. With this
    widening-point set they agree exactly (gated in tests/test_corpus.ml). *)
let reentrant_points (prog : S_syntax.program) : Label.Set.t =
  let acc = ref Label.Set.empty in
  let add l = acc := Label.Set.add l !acc in
  add prog.S_syntax.main;
  List.iter
    (fun (d : S_syntax.fundef) -> add d.S_syntax.entry)
    prog.S_syntax.funs;
  Label.Map.iter
    (fun l (c : S_syntax.cmd) ->
      match c with
      | S_syntax.Return _ | S_syntax.LetCall _ -> add l
      | S_syntax.Let _ | S_syntax.Match _ -> ())
    prog.S_syntax.ctrl;
  !acc

(** Build a handle for [I_S^T] from the interpreter points extracted by
    {!Projection}. Being a pure function of the interpreter text, it is built lazily
    once per functor instance and shared rather than rebuilt per analysis (a
    measurable cost): the record is immutable, and the designated-instance drivers
    refine a {e copy}, [{ h with exact_pins = Some pins }]. *)
let handle_for_interp : unit -> handle =
  let h =
    lazy
      (let pts = Projection.points in
       let eval_call_labels =
         List.fold_left
           (fun acc (l, _) -> Label.Set.add l acc)
           Label.Set.empty
           pts.Projection.Points.call_frames
       in
       {
         prog = Interp_st.program;
         widen_pts = reentrant_points Interp_st.program;
         eval_entry = pts.Projection.Points.eval_entry;
         eval_e = pts.Projection.Points.eval_e;
         eval_call_labels;
         eval_body =
           fun_body_labels Interp_st.program pts.Projection.Points.eval_entry;
         in_scope =
           compute_in_scope Interp_st.program
             [
               ( Interp_st.program.S_syntax.main,
                 [ Interp_st.arg_p; Interp_st.arg_arg ] );
             ];
         exact_pins = None;
         aux = None;
       })
  in
  fun () -> Lazy.force h

(** Build a handle for an arbitrary {e direct} S program — a closed program that is
    {b not} the S-coded T interpreter, so it has no [eval] and no T-view
    sensitivity: the frame index must degenerate to the S label alone. We get that
    without special-casing {!partition_of} by setting [eval_entry] to a sentinel
    label ([-1]) that no real S command can carry (the parser assigns non-negative
    labels), so the eval-entry test never fires, every [t_label] is empty, and the
    eval-only fields are never consulted. *)
let handle_for_program (prog : S_syntax.program) : handle =
  {
    prog;
    widen_pts = reentrant_points prog;
    eval_entry = -1;
    eval_e = "";
    eval_call_labels = Label.Set.empty;
    eval_body = Label.Set.empty;
    in_scope = compute_in_scope prog [ (prog.S_syntax.main, []) ];
    exact_pins = None;
    aux = None;
  }

(** {1 Expression abstraction}

    The abstract expression evaluation [eval#] over S's relaxed-ANF expressions.
    [None] flags an operand the domain cannot evaluate (an uninterpreted primitive,
    or an argument that is itself [None]), on which the concrete machine would be
    stuck; the abstract step then contributes no successor — sound, since there are
    no concrete successors to cover. *)
let rec abs_exp ?(actx : Label.t list = []) (rho : aenv) (e : S_syntax.exp) :
    D.t option =
  match e with
  | S_syntax.EInt n -> Some (D.int_lit n)
  | S_syntax.EVar x -> Some (aenv_find rho x)
  | S_syntax.EPrim (o, es) -> (
      match abs_exps ~actx rho es with Some vs -> D.prim o vs | None -> None)
  | S_syntax.ETag (site, t, es) -> (
      (* The allocation site is the [ETag] node's own parser-assigned label, refined
         by the allocating entry's decoded T context [actx] (retargeted-Sym): one
         interpreter allocation point then yields distinct symbols per T context,
         instead of proxying every T-level allocation context. *)
      match abs_exps ~actx rho es with
      | Some vs ->
          let st =
            if actx = [] then D.Internal site else D.InternalT (site, actx)
          in
          Some (D.tag st t vs)
      | None -> None)

and abs_exps ?(actx : Label.t list = []) (rho : aenv) (es : S_syntax.exp list) :
    D.t list option =
  List.fold_right
    (fun e acc ->
      match (abs_exp ~actx rho e, acc) with
      | Some v, Some vs -> Some (v :: vs)
      | _ -> None)
    es (Some [])

(** {1 Extracting the frame index of a successor} *)

(** All possible T-expression labels of a value, read from field 0 of every encoded
    T-expression tag it may carry: [T_encoding] places an expression's program
    label in field 0 of every expression tag, and the domain keeps that field
    exact, so the labels come back as a precise finite set. *)
let expr_tag_arities : (S_syntax.tag * int) list =
  [
    (T_encoding.tag_int, 2);
    (T_encoding.tag_var, 2);
    (T_encoding.tag_sub, 3);
    (T_encoding.tag_mul, 3);
    (T_encoding.tag_div, 3);
    (T_encoding.tag_mod, 3);
    (T_encoding.tag_lt, 3);
    (T_encoding.tag_let, 4);
    (T_encoding.tag_app, 3);
    (T_encoding.tag_app2, 4);
    (T_encoding.tag_app3, 5);
    (T_encoding.tag_ifz, 4);
  ]

let t_labels_of_value (v : D.t) : Label.Set.t =
  let expr_tags = expr_tag_arities in
  let add_exact (acc : Label.Set.t) (field0 : D.t) : Label.Set.t =
    match D.root_int field0 with
    | D.AFin s ->
        Domain_intf.IntSet.fold (fun n acc -> Label.Set.add n acc) s acc
    (* [AItv]/[ATop] only arise when a numeric value leaked into a label position;
       they contribute no exact label. *)
    | D.AItv _ | D.ABot | D.ATop -> acc
  in
  List.fold_left
    (fun acc (tag, arity) ->
      if D.has_tag tag v then
        (* [fields] is the paper's set of per-site tuples, so the field-0 set is
           the UNION over every tuple; reading only the first tuple's field 0
           would be unsound. *)
        match D.fields tag arity v with
        | Some tuples ->
            List.fold_left
              (fun acc tuple ->
                match tuple with field0 :: _ -> add_exact acc field0 | [] -> acc)
              acc tuples
        | None -> acc
      else acc)
    Label.Set.empty expr_tags

(** Build the frame index of a successor at S label [l] with abstract environment
    [rho] (§impl-t-flow): the T-label component is read from [eval]'s expression
    parameter at every S label where it is in scope (the paper's [Lab_eval]);
    elsewhere [eval_e] reads as bottom and the set is empty.

    {b Soundness of an imprecise or empty t_label.} The t_label is a partition
    {e key} that splits a cover, not a concretization {e filter}: the paper's
    partitioning has [γ_π(σ̂) = γ_δ(σ̂) ∩ δ(π)], and per-step soundness need only
    cover the successors falling in [δ(π')], states landing in other blocks being
    covered by those blocks' entries. A coarser index therefore merely joins more
    entries and never drops a concrete state. This is why mixing T-labels and
    numeric values in one integer lattice is sound: a leaked numeric value adds a
    spurious key, and a field-0 widened to [ATop] collapses the t_label to [∅],
    covering {e all} T-labels; both lose T-sensitivity, neither soundness. *)
let partition_of (h : handle) (l : Label.t) (rho : aenv) : Partition.t =
  let t_label = t_labels_of_value (aenv_find rho h.eval_e) in
  Partition.make ~s_label:l ~t_label

(** Decoder-partiality degradations during the most recent {!solve} (see
    {!t_labels_of_value_exact}). This answers the paper's decoder-totality question:
    under the disambiguated value domain key positions never escape, so the paper
    instance must report [0], while the graded site-keyed mode may degrade soundly.
    Always [0] in the default mode. *)
let last_exact_degrades : int ref = ref 0

(** As {!t_labels_of_value}, but {e demanding} exactness: [Some ls] only when every
    field-0 read is an exact finite set, [None] as soon as a label position has
    escaped to an interval or top or a projection fails.

    The default mode may ignore an escaped read, its T-label being only a partition
    key ({!partition_of}). The designated instance also uses the label as a
    {e filter} — the pin replaces the e-value by the block's abstraction — so a
    state whose read escaped must not be assigned to a pinned block it may not
    inhabit; {!partitions_of} degrades it instead, losing T-sensitivity rather than
    soundness where the state decoder [⌊·⌋] is partial. *)
let t_labels_of_value_exact (v : D.t) : Label.Set.t option =
  let add_exact (acc : Label.Set.t option) (field0 : D.t) : Label.Set.t option =
    match acc with
    | None -> None
    | Some s -> (
        match D.root_int field0 with
        | D.AFin ls ->
            Some
              (Domain_intf.IntSet.fold
                 (fun n acc -> Label.Set.add n acc)
                 ls s)
        | D.ABot -> Some s
        | D.AItv _ | D.ATop -> None)
  in
  List.fold_left
    (fun acc (tag, arity) ->
      match acc with
      | None -> None
      | Some _ ->
          if D.has_tag tag v then
            match D.fields tag arity v with
            | Some tuples ->
                List.fold_left
                  (fun acc tuple ->
                    match tuple with
                    | field0 :: _ -> add_exact acc field0
                    | [] -> acc)
                  acc tuples
            | None -> None
          else acc)
    (Some Label.Set.empty) expr_tag_arities

(** The successor frames of a post-state at S label [l] with post-environment
    [rho], each paired with the (possibly refined) environment it carries.

    Default mode ([h.exact_pins = None]): exactly one successor, {!partition_of}
    with the environment unchanged — the set-valued no-disambiguation mode.

    Designated instance ([Some pins], §impl-t-flow): at an eval-body label
    ([Lab_eval]) the successor is {b split} per single T-label — one frame
    [⟨ℓ, {ℓ_t}⟩] per label of the e-value, realizing [Framê = ⟨ℓ, ℓ_t⟩] as a
    singleton-set invariant over the shared representation — and each split frame's
    environment refines [e] by the exact pin
    [env(⟨ℓ,ℓ_t⟩) = [e ↦ {S^exp_ℓt}·G_max]], the abstraction of the unique
    T-expression node at [ℓ_t]. The split distributes the frame's states over
    disjoint blocks while the other variables keep their joint value, [env]
    constraining only [e]. Away from [Lab_eval] the index is the plain S label, so
    [main]'s glue — whose own variable happens to be named [e] — gets no T-view
    component. If the label read is not exact (decoder partiality) or yields no
    label, the successor degrades to the unsplit, unpinned [⟨ℓ,∅⟩] frame: sound,
    since the T-view key splits a cover and no pin then filters the environment.

    {b Replacement vs meet.} The paper applies [env(φ̂')] as a per-rule meet
    [ρ̂' ⊓ env(φ̂')]; here the [e ↦ pin] {e replacement} happens at the split and the
    in-scope restriction in {!refine_succ}. The replacement is sound because the
    split key is also the partition filter (every state assigned to [⟨ℓ,{ℓ_t}⟩] has
    [ρ(e) ∈ γ(pin)]), and it equals the meet whenever the flowing e-value dominates
    the pin — always so under the disambiguated domain, where the block is inhabited
    by the unique encoded node at [ℓ_t]. *)
let partitions_of (h : handle) (l : Label.t) (rho : aenv) :
    (Partition.t * aenv) list =
  match h.exact_pins with
  | None -> [ (partition_of h l rho, rho) ]
  | Some pins ->
      let unsplit () =
        [ (Partition.make ~s_label:l ~t_label:Label.Set.empty, rho) ]
      in
      if not (Label.Set.mem l h.eval_body) then unsplit ()
      else begin
        match t_labels_of_value_exact (aenv_find rho h.eval_e) with
        | None ->
            incr last_exact_degrades;
            unsplit ()
        | Some ls when Label.Set.is_empty ls -> unsplit ()
        | Some ls ->
            List.map
              (fun lt ->
                let phi =
                  Partition.make ~s_label:l ~t_label:(Label.Set.singleton lt)
                in
                let rho' =
                  match Label.Map.find_opt lt pins with
                  | Some pv -> aenv_add h.eval_e pv rho
                  | None -> rho
                in
                (phi, rho'))
              (Label.Set.elements ls)
      end

(** The decoded-T allocation context of an entry [⟨φ̂, κ̂⟩ ↦ …]: the T labels of its
    own frame index when present, otherwise those stashed in its continuation index
    [κ̂] — the case inside the auxiliaries, whose frame index carries no T label but
    whose continuation index was pushed with the calling eval body's T-context (see
    {!push}). Deliberately a function of the table {e key} alone: the stored
    continuation set grows as callers accumulate, so reading it would make symbol
    naming depend on the worklist's update order. Sorted, hence canonical. *)
let actx_of (phi : Partition.t) (k : kidx) : Label.t list =
  let t = phi.Partition.t_label in
  if not (Label.Set.is_empty t) then Label.Set.elements t
  else match k with KBullet -> [] | KTLabs s -> Label.Set.elements s

(** {1 The view-indexed abstract step}

    From one entry [π̂ ↦ ⟨ρ̂, κ̂⟩] at S label [lab(φ̂)], emit the successor entries
    to be joined into the table, realizing the local rules
    [AbsLetExp]/[AbsLetCall]/[AbsReturn]/[AbsMatch]. A constructor allocation is
    folded into [AbsLetExp] (the [ETag] case of {!abs_exp}). *)

(** A pending successor: the post-key [⟨φ̂', κ̂'⟩], the post-environment [ρ̂']
    (before the [⊓ env] refinement), and the post-kont. *)
type succ = Key.t * aenv * kont

let find_fun (h : handle) (f : S_syntax.var) : S_syntax.fundef option =
  List.find_opt
    (fun (d : S_syntax.fundef) -> String.equal d.S_syntax.name f)
    h.prog.S_syntax.funs

(** The abstract push [pusĥ : Framê × Kont̂ → Kont̂] of the retargeted analysis: a
    case analysis on the call site of the caller frame [φ̂], given the invoked
    function [def]. An eval-call ([Lab_call ∪ {maineval}]) resets the context to
    [•], the callee's T-view being carried by its frame index. An auxiliary call
    from [eval]'s own body ([Lab_auxcall ∩ Lab_eval], realized by
    {!fun_body_labels} — see its doc for why a name-scope test on [e] is wrong)
    stashes the current T-context [φ̂.t_label] into the continuation index, since
    the auxiliary body has no [e] to carry it. Any other auxiliary call
    ([Lab_aux ∪ (Lab_auxcall ∖ Lab_eval)]) already has the context in [κ̂] and
    leaves it unchanged.

    For a direct-S program the first two cases never fire, so every push leaves
    [κ̂ = •] — context-insensitive returns. *)
let push (h : handle) (phi : Partition.t) (def : S_syntax.fundef) (kidx : kidx) :
    kidx =
  let k' =
    if Label.equal def.S_syntax.entry h.eval_entry then KBullet
    else if Label.Set.mem (Partition.lab phi) h.eval_body then
      KTLabs phi.Partition.t_label
    else kidx
  in
  (* Enforce the designated instance's single-ℓ_t invariant at the production
     site: [partitions_of] only builds singleton or empty frame views and this push
     only copies them, so a wider set here is a bug, not an imprecision. Fail fast
     rather than let it silently coarsen the instance. *)
  (match (h.exact_pins, k') with
  | Some _, KTLabs s when Label.Set.cardinal s > 1 ->
      invalid_arg
        "S_abstract.push: single-label invariant violated at the designated \
         instance"
  | _ -> ());
  k'

(** The successors of one entry [⟨φ̂,κ̂⟩ ↦ ⟨ρ̂,κ̂-set⟩]. [sigma] is the whole current
    state, which [AbsReturn] needs in order to read the caller's stored entry. *)
let step_entry (h : handle) (sigma : state) ((phi, k) : Key.t) (rho : aenv)
    (kont : kont) : succ list =
  let l = Partition.lab phi in
  let actx = actx_of phi k in
  match S_syntax.cmd_at h.prog l with
  | S_syntax.Return a -> (
      (* [AbsReturn]. Resume each caller part ⟨φ̂_c,κ̂_c⟩ of the stored continuation
         set: its entry is read by a precise key lookup, the result variable is
         bound in the caller's saved environment, and the successor carries the
         caller's own stored continuation and index κ̂_c. [•] is the program result:
         nothing to return into. *)
      match abs_exp ~actx rho a with
      | None -> []
      | Some v ->
          List.concat_map
            (fun (e : kelem) ->
              match e with
              | KEmpty -> []
              | KPart caller -> (
                  let phi_c = caller.pphi and kidx_c = caller.pkont in
                  match S_syntax.cmd_at h.prog (Partition.lab phi_c) with
                  | S_syntax.LetCall (x, _f, _args, cont) -> (
                      match Table.find_opt (phi_c, kidx_c) sigma with
                      | None -> []
                      | Some centry ->
                          let rho_c = aenv_add x v centry.rho in
                          List.map
                            (fun (phi', rho_c') : succ ->
                              ((phi', kidx_c), rho_c', centry.kont))
                            (partitions_of h cont rho_c))
                  | _ -> []))
            kont)
  | S_syntax.Let (x, r, cont) -> (
      (* [AbsLetExp]: bind [x] to the abstracted RHS (which also covers an [ETag]
         constructor allocation) and continue at [cont] under the same
         continuation. *)
      match abs_exp ~actx rho r with
      | None -> []
      | Some v ->
          let rho' = aenv_add x v rho in
          List.map
            (fun (phi', rho'') -> ((phi', k), rho'', kont))
            (partitions_of h cont rho'))
  | S_syntax.LetCall (x, f, args, cont) -> (
      match h.aux with
      | Some cfg when List.exists (String.equal f) cfg.aux_names -> (
          (* Folded auxiliary macro-step (opt-in): discharge the call by the
             [def:auxop] transfer operator, bind [x] to the result, and resume
             [cont] under the caller's own [(k, kont)] — no callee entry, no aux
             cells. [None] (a stuck helper run) yields no successor. *)
          match abs_exps ~actx rho args with
          | None -> []
          | Some arg_vals -> (
              let r =
                match cfg.aux_op with
                | Closed denot -> denot f arg_vals
                | Delimited -> (
                    match find_fun h f with
                    | None -> None
                    | Some def -> !delimited_hook h cfg k def arg_vals)
              in
              match r with
              | None -> []
              | Some v ->
                  let rho' = aenv_add x v rho in
                  List.map
                    (fun (phi', rho'') -> ((phi', k), rho'', kont))
                    (partitions_of h cont rho')))
      | _ -> (
          (* [AbsLetCall]. The callee's single stored caller part is the current
             ⟨φ̂,κ̂⟩, carrying its real continuation index κ̂ = [k] so that [AbsReturn]
             can look it up precisely; the callee entry is indexed by
             κ̂' = pusĥ(φ̂, κ̂). The result variable and continuation label are
             recovered later by [AbsReturn] from this same [LetCall]. *)
          match find_fun h f with
          | None -> []
          | Some def -> (
              match abs_exps ~actx rho args with
              | None -> []
              | Some arg_vals ->
                  if List.length def.S_syntax.params <> List.length arg_vals then
                    []
                  else
                    let callee_rho =
                      List.fold_left2
                        (fun e param v -> aenv_add param v e)
                        aenv_empty def.S_syntax.params arg_vals
                    in
                    let kidx' = push h phi def k in
                    let callee_kont = [ KPart { pphi = phi; pkont = k } ] in
                    List.map
                      (fun (phi', callee_rho') ->
                        ((phi', kidx'), callee_rho', callee_kont))
                      (partitions_of h def.S_syntax.entry callee_rho))))
  | S_syntax.Match (a, branches) -> (
      (* [AbsMatch]: the rule is existentially quantified over
         [⟨v̄_i⟩ ∈ fields#_T(...)], so each possible branch emits ONE successor per
         tuple of [fields#_T(tag,arity,scrut)]. Distinct allocation sites of one tag
         thus yield distinct successors, keeping fields relationally paired. *)
      match abs_exp ~actx rho a with
      | None -> []
      | Some scrut ->
      List.concat_map
        (fun (S_syntax.PTag (tag, vars), cont) ->
          let arity = List.length vars in
          if D.has_tag tag scrut then
            match D.fields tag arity scrut with
            | Some tuples ->
                List.concat_map
                  (fun tuple ->
                    if List.length tuple = arity then
                      (* γ-preserving GC of the projected field grammar (the paper
                         garbage-collects the grammar component of a field value): a
                         projected field carries the whole parent grammar, so a
                         [Match]-bound variable would otherwise hold the entire
                         encoded-program grammar — the dominant bloat source. *)
                      let rho' =
                        List.fold_left2
                          (fun e y v -> aenv_add y (D.gc v) e)
                          rho vars tuple
                      in
                      List.map
                        (fun (phi', rho'') -> ((phi', k), rho'', kont))
                        (partitions_of h cont rho')
                    else [])
                  tuples
            | None -> []
          else [])
        branches)

(** {1 Worklist fixpoint}

    The analysis is the least fixpoint of the full transfer function (the join of
    the view-indexed steps), computed by a worklist: process an entry, push each
    refined successor into the table (joining, or widening on a re-visit at a
    reentrant point), and enqueue every entry whose successors must be recomputed.
    Because [AbsReturn] reads the caller's entry out of the table, a [Return] whose
    caller entry grows must be re-processed even though its own value did not
    change; {!dependents} expands a changed key into exactly those keys. *)

(** The write-back refinement of a raw successor (folded into each local rule):
    refine the environment by [⊓ env(φ̂')], a restriction to the variables in scope
    at [φ̂']. There is no [∩ pusĥ⁻¹(κ̂')] continuation filter, because each rule
    produces the exact post continuation index directly ([pusĥ] forward at a call,
    the caller's stored κ̂_c on return). *)
let refine_succ (h : handle) (((phi', k'), rho', kont') : succ) : succ =
  let rho_ref = aenv_meet_scope rho' (env_of_frame h phi') in
  ((phi', k'), rho_ref, kont')

(** Is [key] a caller-frame entry, i.e. a [LetCall]? Any call, eval-call or
    auxiliary, stores a caller part. *)
let is_caller_key (h : handle) ((phi, _) : Key.t) : bool =
  match S_syntax.cmd_at h.prog (Partition.lab phi) with
  | S_syntax.LetCall _ -> true
  | _ -> false

let kont_mentions_part (k : kont) (cpk : Key.t) : bool =
  List.exists
    (fun (e : kelem) ->
      match e with
      | KEmpty -> false
      | KPart p -> Key.compare (p.pphi, p.pkont) cpk = 0)
    k

(** The entries whose successors must be recomputed now that [key]'s stored value
    grew: [key] itself, plus — when [key] is a caller-frame entry — every [Return]
    entry whose stored continuation names that caller part, i.e. exactly those whose
    [AbsReturn] reads [σ̂(⟨φ̂_c,κ̂_c⟩)]. Without this reverse edge such a [Return]
    would keep a stale value strictly below the fixpoint (in particular when its
    caller part is created after the return was first processed): the
    worklist-completeness invariant of [AbsReturn]. *)
let dependents ?(idx : index option) (h : handle) (sigma : state) (key : Key.t) :
    Key.t list =
  if is_caller_key h key then
    match idx with
    | Some idx ->
        (* The reverse index holds exactly the [Return] keys naming [key]; the
           table scan below computes the same set. *)
        KeySet.fold (fun k acc -> k :: acc) (keymap_find_set idx.rev key) [ key ]
    | None ->
        Table.fold
          (fun ((rphi, _) as rkey) (rentry : entry) acc ->
            if kont_mentions_part rentry.kont key then
              match S_syntax.cmd_at h.prog (Partition.lab rphi) with
              | S_syntax.Return _ -> rkey :: acc
              | _ -> acc
            else acc)
          sigma [ key ]
  else [ key ]

(** Join (or, on re-visit at a widening key, widen) a refined successor into the
    table at its key; return the updated table and whether the stored entry grew.
    The environment is joined/widened pointwise; the continuation set is unioned (it
    ranges over a finite set, so it stabilizes without widening). Bottom-strict: an
    entry with an empty environment {e and} empty continuation contributes nothing.
    The optional index [idx] is a mutable side view of [sigma] kept in step here;
    updating it changes neither the returned table nor the [grew] flag. *)
let update ?(idx : index option) ?(widen_at : (Key.t -> bool) option)
    (sigma : state) (((key, rho, kont) : succ)) : state * bool =
  if Env.is_empty rho && kont_is_empty kont then (sigma, false)
  else
    match Table.find_opt key sigma with
    | None ->
        (match idx with
        | Some idx -> idx_record idx key ~old_kont:[] ~new_kont:kont
        | None -> ());
        (Table.add key { rho; kont } sigma, true)
    | Some old ->
        (* Growth detection without building the joined/widened environment. The
           stored value grows exactly when [¬(rho ⊑ old.rho)], equivalently when
           [¬(aenv_widen old.rho (aenv_join old.rho rho) ⊑ old.rho)]: if
           [rho ⊑ old.rho] the join is [old.rho] and the self-widening stays there,
           otherwise the join strictly grows and the widening preserves that growth.
           Testing up front avoids materialising the (large) joined and widened
           environments on the common no-growth re-visit. *)
        let grew_rho = not (aenv_leq rho old.rho) in
        let new_kont = kont_union old.kont kont in
        let grew_kont = compare_kont new_kont old.kont <> 0 in
        if (not grew_rho) && not grew_kont then (sigma, false)
        else begin
          (* Only on a real write build the joined/widened environment, exactly as
             the unfused [aenv_widen old.rho (aenv_join old.rho rho)]. [widen_at]
             (default: widen at every revisited key) restricts widening to the keys
             it accepts; {!solve} passes the reentrant points. *)
          let joined_rho = aenv_join old.rho rho in
          let widened_rho =
            match widen_at with
            | Some at when not (at key) -> joined_rho
            | _ -> aenv_widen old.rho joined_rho
          in
          (match idx with
          | Some idx when grew_kont ->
              idx_record idx key ~old_kont:old.kont ~new_kont
          | _ -> ());
          (Table.add key { rho = widened_rho; kont = new_kont } sigma, true)
        end

(** Worklist pops of the most recent {!solve} on this instance — a read-out for
    the bench harness, not part of the analysis semantics. *)
let last_solve_steps : int ref = ref 0

(** Run the worklist to convergence from an initial table [init], returning the
    least-fixpoint table. [max_steps] bounds the entry processings as a defensive
    guard; by the finiteness and widening arguments above it is never the binding
    limit. *)
let solve ?(max_steps = 5_000_000) ?(step = step_entry)
    ?(passive : (Key.t -> bool) option) ?(widen_at : (Key.t -> bool) option)
    (h : handle) (init : state) : state =
  last_exact_degrades := 0;
  (* Widen at the reentrant points and nowhere else; [~widen_at] overrides the set
     (the gates use it to exhibit the coarser every-key schedule). *)
  let widen_at =
    match widen_at with
    | Some f -> f
    | None ->
        fun ((phi, _) : Key.t) ->
          Label.Set.mem (Partition.lab phi) h.widen_pts
  in
  let module KeySet = Set.Make (Key) in
  (* The reverse dependency index: seeded from [init], maintained by [update],
     consulted by [dependents]. *)
  let idx =
    index_of_state
      (fun phi ->
        match S_syntax.cmd_at h.prog (Partition.lab phi) with
        | S_syntax.Return _ -> true
        | _ -> false)
      init
  in
  let initial_keys =
    Table.fold (fun key _ acc -> KeySet.add key acc) init KeySet.empty
  in
  let rec loop steps sigma worklist =
    if steps <= 0 then
      failwith "S_abstract.solve: step budget exhausted (non-termination?)"
    else
      match KeySet.choose_opt worklist with
      | None ->
          last_solve_steps := max_steps - steps;
          sigma
      | Some key ->
          let worklist = KeySet.remove key worklist in
          let e = table_find sigma key in
          let succs = step h sigma key e.rho e.kont in
          let sigma', changed_keys =
            List.fold_left
              (fun (sg, chg) raw ->
                let succ = refine_succ h raw in
                let sg', changed = update ~idx ~widen_at sg succ in
                let key', _, _ = succ in
                if changed then
                  ( sg',
                    (* [passive] keys are write-only records of the caller's step
                       discipline (frames the specialized transfer records but never
                       steps from), so popping them yields no successors: drop the
                       self edge, keep the reverse (Return) edges. [None] (the
                       default) preserves the base behavior exactly. *)
                    List.fold_left
                      (fun acc k ->
                        match passive with
                        | Some f when f k -> acc
                        | _ -> KeySet.add k acc)
                      chg
                      (dependents ~idx h sg' key') )
                else (sg', chg))
              (sigma, KeySet.empty) succs
          in
          loop (steps - 1) sigma' (KeySet.union worklist changed_keys)
  in
  loop max_steps init initial_keys

(** {1 Driver: abstractly analyze [I_S^T] on an encoded T program}

    Analogous to {!Interp_st.eval_t} but abstract: seed [main]'s environment with the
    encoded T program and an abstract argument, run the fixpoint, read the result
    back from the table. *)

(** The converged table and the abstract value the program returns. *)
type analysis = { table : state; result : D.t }

let initial_env (encoded_p : D.t) (arg : D.t) : aenv =
  aenv_add Interp_st.arg_p encoded_p (aenv_add Interp_st.arg_arg arg aenv_empty)

(** Base offset for the allocation sites given to the nodes of the fully-known
    input value, kept well above the interpreter's own command and [ETag] labels so
    a syntax-node site never collides with an interpreter allocation site. *)
let input_site_base = 1_000_000

(** Abstract a concrete S value into the domain, also recording for every encoded
    T-expression node the abstraction of the sub-value rooted there, keyed by its T
    label — the per-label pins of the paper's [env(⟨ℓ,ℓ_t⟩)] (see {!partitions_of}).
    A tagged value is rebuilt with a {e fresh, distinct} allocation site per node,
    so the statically-known input becomes a precise finite tree grammar with one
    symbol per syntax node. The pins are recorded in the {e same} traversal and so
    share those allocation sites: the pin for [ℓ_t] {b is} the sub-abstraction of the
    input at that node. Duplicate labels (impossible here) would be joined. *)
let abstract_value_pins (v : S_cek.value) : D.t * D.t Label.Map.t =
  let next = ref input_site_base in
  let fresh_site () =
    let l = !next in
    incr next;
    D.Internal l
  in
  let pins = ref Label.Map.empty in
  let rec go (v : S_cek.value) : D.t =
    match v with
    | S_cek.VInt n -> D.int_lit n
    | S_cek.VTag (t, vs) ->
        let dv = D.tag (fresh_site ()) t (List.map go vs) in
        (match (List.mem_assoc t expr_tag_arities, vs) with
        | true, S_cek.VInt l :: _ ->
            pins :=
              Label.Map.update l
                (function None -> Some dv | Some old -> Some (D.join old dv))
                !pins
        | _ -> ());
        dv
  in
  let root = go v in
  (root, !pins)

(** Abstract a concrete S value into the domain (the pins discarded). *)
let abstract_value (v : S_cek.value) : D.t = fst (abstract_value_pins v)

(** Read the abstract program result from a converged table: the join, over every
    entry sitting at a [Return] under the empty continuation [{•}], of the value
    returned. *)
let read_result (h : handle) (sigma : state) : D.t =
  Table.fold
    (fun (phi, kx) (e : entry) acc ->
      if List.exists (fun el -> compare_kelem el KEmpty = 0) e.kont then
        match S_syntax.cmd_at h.prog (Partition.lab phi) with
        | S_syntax.Return a -> (
            match abs_exp ~actx:(actx_of phi kx) e.rho a with
            | Some v -> D.join acc v
            | None -> acc)
        | _ -> acc
      else acc)
    sigma D.bottom

(** The [Delimited] auxiliary summary: the base analysis of the callee body in a
    {e fresh} table, seeded like [AbsLetCall]'s callee entry but with the local-halt
    continuation [{•}] and read back at [•] like a program result. The sub-solve runs
    the plain base ([aux = None]), so the helper's own recursion is this delimited
    fixpoint rather than a nested summary. Memoized per [(name, κ̂, args)]; a bottom
    summary means no run reaches a return (concretely stuck), hence no successor. *)
let delimited_summary (h : handle) (cfg : aux_config) (kidx : kidx)
    (def : S_syntax.fundef) (args : D.t list) : D.t option =
  let key = (def.S_syntax.name, kidx, args) in
  match Hashtbl.find_opt cfg.aux_memo key with
  | Some r -> r
  | None ->
      let r =
        if List.length def.S_syntax.params <> List.length args then None
        else
          let callee_rho =
            List.fold_left2
              (fun e p v -> aenv_add p v e)
              aenv_empty def.S_syntax.params args
          in
          let hbase = { h with aux = None } in
          let phi = partition_of hbase def.S_syntax.entry callee_rho in
          let init =
            Table.add (phi, kidx)
              { rho = callee_rho; kont = kont_halt }
              state_empty
          in
          let table = solve hbase init in
          let v = read_result hbase table in
          if D.is_bottom v then None else Some (D.gc v)
      in
      Hashtbl.replace cfg.aux_memo key r;
      r

let () = delimited_hook := delimited_summary

(** Abstractly analyze the S-coded T interpreter on the encoded T program
    [encoded_p] with abstract argument [arg]. [~exact:true] runs the designated
    instance (see {!partitions_of}), whose per-label pins are read off the same
    traversal that builds the initial program value. *)
let analyze ?(arg : D.t = D.int_lit 0) ?(exact = false)
    ?(aux : aux_config option = None) ?(widen_at : (Key.t -> bool) option)
    (encoded_p : S_cek.value) : analysis =
  let h0 = handle_for_interp () in
  let pv, pins = abstract_value_pins encoded_p in
  let h = if exact then { h0 with exact_pins = Some pins } else h0 in
  let h = { h with aux } in
  let rho0 = initial_env pv arg in
  let phi0 = partition_of h h.prog.S_syntax.main rho0 in
  let init =
    Table.add (phi0, KBullet) { rho = rho0; kont = kont_halt } state_empty
  in
  let table = solve ?widen_at h init in
  { table; result = read_result h table }

(** Analyze a T program (in the {!T_encoding} AST) by encoding it first, exactly as
    {!Interp_st.eval_t} does for the concrete run. *)
let analyze_t ?(arg : D.t = D.int_lit 0) ?(exact = false)
    ?(aux : aux_config option = None) ?(widen_at : (Key.t -> bool) option)
    (p : T_encoding.program) : analysis =
  analyze ~arg ~exact ~aux ?widen_at (T_encoding.enc_program p)

(** Analyze with an externally supplied per-entry step function — the generated
    (stored-code) form of {!step_entry}, specialized w.r.t. the interpreter text.
    Seeding, solving, widening, and scheduling are the {e same code} as {!analyze},
    so a comparison against it isolates exactly what specializing the step buys. *)
let analyze_with
    ~(step : handle -> state -> Key.t -> aenv -> kont -> succ list)
    ?(passive : (Key.t -> bool) option)
    ?(arg : D.t = D.int_lit 0) ?(exact = false) (encoded_p : S_cek.value) :
    analysis =
  let h0 = handle_for_interp () in
  let pv, pins = abstract_value_pins encoded_p in
  let h = if exact then { h0 with exact_pins = Some pins } else h0 in
  let rho0 = initial_env pv arg in
  let phi0 = partition_of h h.prog.S_syntax.main rho0 in
  let init =
    Table.add (phi0, KBullet) { rho = rho0; kont = kont_halt } state_empty
  in
  let table = solve ~step ?passive h init in
  { table; result = read_result h table }

let analyze_t_with ~step ?(passive : (Key.t -> bool) option)
    ?(arg : D.t = D.int_lit 0) ?(exact = false) (p : T_encoding.program) :
    analysis =
  analyze_with ~step ?passive ~arg ~exact (T_encoding.enc_program p)

(** {1 Driver: abstractly analyze an arbitrary direct S program}

    The counterpart of {!analyze} for a {e direct} S program. The concrete machine
    runs such a program from [main] with the empty environment and continuation
    ({!S_cek.inject}); the abstract analysis mirrors that seed over abstract values
    and runs the same {!solve} and the same {!step_entry}, the only difference being
    the handle ({!handle_for_program}), under which the frame index degenerates to
    the S label. *)

(** Abstractly analyze a closed direct S program from [main] (empty initial
    environment, halt continuation), returning the converged table. *)
let analyze_prog (prog : S_syntax.program) : state =
  let h = handle_for_program prog in
  let phi0 = partition_of h prog.S_syntax.main aenv_empty in
  let init =
    Table.add (phi0, KBullet) { rho = aenv_empty; kont = kont_halt } state_empty
  in
  solve h init

(** The abstract result of a direct-S analysis: {!read_result} specialized to a
    direct-S program. It needs only the program text, so it rebuilds a (cheap)
    handle internally. *)
let prog_result (prog : S_syntax.program) (sigma : state) : D.t =
  read_result (handle_for_program prog) sigma

(** {1 Inspection helpers: accessors used by tests and drivers} *)

let table_size (sigma : state) : int = Table.cardinal sigma

let partitions (sigma : state) : Partition.Set.t =
  Table.fold (fun (phi, _) _ acc -> Partition.Set.add phi acc) sigma
    Partition.Set.empty

(** Whether any table entry's frame index has the given S label and carries the
    given T label. Used to demonstrate T-sensitivity. *)
let has_partition_with_t_label (sigma : state) ~(s_label : Label.t)
    ~(t_label : Label.t) : bool =
  Table.exists
    (fun (phi, _) _ ->
      Label.equal (Partition.lab phi) s_label
      && Label.Set.mem t_label phi.Partition.t_label)
    sigma

end

(** Default instantiation: the concrete RTG value domain. The [include] re-exports
    the functor body's types, values, and submodules at the {!S_abstract} top
    level. *)
include Make (Domain_rtg)
