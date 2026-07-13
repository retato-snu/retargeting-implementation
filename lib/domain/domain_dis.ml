(** Domain disambiguation — the paper's program-derived construction
    (§"Domain Disambiguation", [sec:disamb]) as a {!Domain_intf.DOMAIN} instance.

    It realizes both layers of the construction. The abstract tree grammars for
    reified objects (§[sec:abs-objects]) — label-refined AST symbols [T_ℓt],
    name-refined environment symbols [Bind_x], name-keyed definition symbols —
    become the program-derived partition symbols [S^exp_ℓ] / [S^var_x] /
    [S^fun_f] below. Positional domain disambiguation (§[sec:posdisamb]) enters
    through the role map {!Role}: {!tag} routes a construction on the integer-key
    field the map designates ([Label]/[Var]/[Fname], via [key_spec]), key
    constants are injected through the role-appropriate base domain
    ([int_of_role] = the paper's [int(α_r{c})]), and the [lookup]/[fundef] key
    comparisons are the role-annotated identifier equalities [key_eq]
    ([==_{var,var}] / [==_{fname,fname}]), distinct from the numeric
    [==_{num,num}] and arithmetic of {!Make.prim}. The role [Num] uses the
    swappable numeric base domain, here the graded {!Domain_intf.aint}.

    {1 The construction}

    A tree-grammar domain already tells apart the different natures the one
    S-integer type stands for — several symbols may share a tag, each with its
    own abstract integer per argument position — so, per the paper, "it only
    remains to choose the symbols". They are chosen from the constants of the
    fixed T program [P]: [Fun_P] (defined function names), [Var_P] (variable
    names, plus the implicit parameter name [0]) and [Lab_P] (labels, each
    identifying one labeled subterm and hence one encoding tag [tag_P(ℓ)]),
    giving [Sym = {S^fun_f} ∪ {S^var_x} ∪ {S^exp_ℓ}] — [defs] conses keyed by
    function name, [env] conses by binder, [exp] nodes by label — plus the
    nullary symbols, the [Prog] wrapper, and one garbage symbol [S_?] per
    remaining tag for the paper's [★]-keyed block (never populated on well-formed
    input; it only keeps the partition a rectangular disjoint cover). A key
    position holds the exact finite block routed on — a keyed symbol's key field
    pinned to its singleton [{c}] (the paper's [Fin(C_P)] atom), a garbage
    symbol's to the residual — while a genuine T-value position (the [Int]
    literal, the [Extend] value slot) keeps the base numeric domain. [Sym] and
    the key blocks are computed from [P] before the fixpoint (this functor's
    initialization); [G_max]'s unconstrained non-key positions are realized by
    the ordinary grammar join/widen, whose chains are finite over the
    program-derived symbol space, so no ceiling need be materialized.

    {1 Routing at construction}

    {!Make.tag} routes on the constructed value's first argument — the
    identifying T-entity every non-nullary tag stores there — ignoring the
    allocation {e site}: an exact collected key goes to its single symbol, a
    joined key degrades to the union over the candidate symbols (never to top),
    and a non-collected residual goes to the tag's garbage symbol. This is sound
    because any concrete [T(c, v̄)] with [c ∈ γ(key-arg)] is a member of the
    result: [c] routes to a symbol whose key field contains it (its own singleton
    if collected, else the residual block) and whose remaining fields
    over-approximate the argument values — the reading {!Make.mem} realizes.

    Both sides of the [lookup]/[fundef] key comparisons are therefore
    singleton-exact abstract integers, so each is decided exactly: [lookup]
    returns just the requested slot [v̂_x] and [fundef] just the body
    [⟨⊥, {S^exp_ℓf}⟩], whether the auxiliaries are {e analyzed} through the
    abstract S machine (per-symbol [fields] tuples keep key and payload
    relationally paired) or {e folded} to the abstract denotations
    ({!Make.aux_denot}).

    {b Value sensitivity is intentionally paper-only:} the [Bind_{x,i}]
    refinement of §[sec:posdisamb] / §[sec:value-sens], which keys environment
    conses additionally by a numeric invariant [N_i], is not implemented here
    ([SVar of int] keys by binder name only, and {!Partition.t} carries no
    [(ℓt,i)] component), matching the paper's {e measured} scope. *)

module IntSet = Domain_intf.IntSet
module T = T_encoding

type aint = Domain_intf.aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

type site = Domain_intf.site =
  | Internal of Label.t
  | InternalT of Label.t * Label.t list
  | External

let ajoin = Domain_rtg.aint_join
let awiden = Domain_rtg.aint_widen
let aleq = Domain_rtg.aint_leq

module Make (P : sig
  val prog : T.program
end) =
struct
  type nonrec aint = aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

  type nonrec site = site =
    | Internal of Label.t
    | InternalT of Label.t * Label.t list
    | External

  let aint_mem = Domain_rtg.aint_mem

  (** {1 Collected constants} *)

  let label_of : T.expr -> Label.t = function
    | T.Int (l, _)
    | T.Var (l, _)
    | T.Add (l, _, _)
    | T.Sub (l, _, _)
    | T.Mul (l, _, _)
    | T.Div (l, _, _)
    | T.Mod (l, _, _)
    | T.Lt (l, _, _)
    | T.Let (l, _, _, _)
    | T.App (l, _, _)
    | T.App2 (l, _, _, _)
    | T.App3 (l, _, _, _, _)
    | T.Ifz (l, _, _, _) ->
        l

  let tag_of : T.expr -> S_syntax.tag = function
    | T.Int _ -> T.tag_int
    | T.Var _ -> T.tag_var
    | T.Add _ -> T.tag_add
    | T.Sub _ -> T.tag_sub
    | T.Mul _ -> T.tag_mul
    | T.Div _ -> T.tag_div
    | T.Mod _ -> T.tag_mod
    | T.Lt _ -> T.tag_lt
    | T.Let _ -> T.tag_let
    | T.App _ -> T.tag_app
    | T.App2 _ -> T.tag_app2
    | T.App3 _ -> T.tag_app3
    | T.Ifz _ -> T.tag_ifz

  (** [tag_P]: label ↦ the tag of the labeled subterm of [P] it identifies. *)
  let tag_p : (Label.t, S_syntax.tag) Hashtbl.t = Hashtbl.create 64

  let fun_p = ref IntSet.empty
  let var_p = ref IntSet.empty (* vars occurring, plus the parameter name 0 *)

  let () =
    let rec walk (e : T.expr) : unit =
      Hashtbl.replace tag_p (label_of e) (tag_of e);
      match e with
      | T.Int _ -> ()
      | T.Var (_, x) -> var_p := IntSet.add x !var_p
      | T.Add (_, a, b) | T.Sub (_, a, b) | T.Mul (_, a, b) ->
          walk a;
          walk b
      | T.Div (_, a, b) | T.Mod (_, a, b) | T.Lt (_, a, b) ->
          walk a;
          walk b
      | T.Let (_, x, a, b) ->
          var_p := IntSet.add x !var_p;
          walk a;
          walk b
      | T.App (_, _, a) -> walk a
      | T.App2 (_, _, a, b) ->
          walk a;
          walk b
      | T.App3 (_, _, a, b, c) ->
          walk a;
          walk b;
          walk c
      | T.Ifz (_, a, b, c) ->
          walk a;
          walk b;
          walk c
    in
    var_p := IntSet.singleton 0;
    List.iter
      (fun (f, body) ->
        fun_p := IntSet.add f !fun_p;
        walk body)
      P.prog.T.defs;
    walk P.prog.T.main

  let fun_p : IntSet.t = !fun_p
  let var_p : IntSet.t = !var_p

  (** [Lab_P(T)]: the collected labels per encoding tag (the per-tag label
      blocks), precomputed once from [tag_P]. *)
  let labs_by_tag : (S_syntax.tag, IntSet.t) Hashtbl.t =
    let h = Hashtbl.create 8 in
    Hashtbl.iter
      (fun l t ->
        let old =
          match Hashtbl.find_opt h t with Some s -> s | None -> IntSet.empty
        in
        Hashtbl.replace h t (IntSet.add l old))
      tag_p;
    h

  (** {1 Partition symbols} *)

  type sym =
    | SFun of int  (** [S^fun_f]: a [defs] cons keyed by function name *)
    | SVar of int  (** [S^var_x]: an [env] cons keyed by binder *)
    | SExp of Label.t  (** [S^exp_ℓ]: an [exp] node keyed by label *)
    | SEof
    | SEmpty
    | STrue
    | SFalse
    | SProg
    | SGarb of S_syntax.tag
        (** the [★]-keyed garbage block of a tag (never populated on
            well-formed input; kept for a total, rectangular cover) *)

  let sym_tag : sym -> S_syntax.tag = function
    | SFun _ -> T.tag_fun
    | SVar _ -> T.tag_extend
    | SExp l -> (
        match Hashtbl.find_opt tag_p l with Some t -> t | None -> "?")
    | SEof -> T.tag_eof
    | SEmpty -> T.tag_empty
    | STrue -> "True"
    | SFalse -> "False"
    | SProg -> T.tag_prog
    | SGarb t -> t

  let string_of_sym : sym -> string = function
    | SFun f -> Printf.sprintf "S^fun_%d" f
    | SVar x -> Printf.sprintf "S^var_%d" x
    | SExp l -> Printf.sprintf "S^exp_%d" l
    | SEof -> "S_Eof"
    | SEmpty -> "S_Empty"
    | STrue -> "S_True"
    | SFalse -> "S_False"
    | SProg -> "S_Prog"
    | SGarb t -> Printf.sprintf "S_?%s" t

  module Sym = struct
    type t = sym

    let compare = Stdlib.compare
  end

  module SymSet = Set.Make (Sym)
  module Gram = Map.Make (Sym)

  (** {1 Nodes, grammars, values — the tree-grammar carrier} *)

  type node = { ai : aint; syms : SymSet.t }
  type gram = node list Gram.t
  type t = { root : node; gram : gram }

  let node_bot : node = { ai = ABot; syms = SymSet.empty }

  let node_leq (a : node) (b : node) : bool =
    aleq a.ai b.ai && SymSet.subset a.syms b.syms

  let node_join (a : node) (b : node) : node =
    if a == b then a
    else { ai = ajoin a.ai b.ai; syms = SymSet.union a.syms b.syms }

  let node_widen (a : node) (b : node) : node =
    if a == b then a
    else { ai = awiden a.ai b.ai; syms = SymSet.union a.syms b.syms }

  let rec combine_prod (f : node -> node -> node) (xs : node list)
      (ys : node list) : node list =
    match (xs, ys) with
    | [], [] -> []
    | x :: xs', y :: ys' ->
        let z = f x y in
        let zs = combine_prod f xs' ys' in
        if z == x && zs == xs' then xs else z :: zs
    | x :: xs', [] ->
        let z = f x node_bot in
        let zs = combine_prod f xs' [] in
        if z == x && zs == xs' then xs else z :: zs
    | [], y :: ys' -> f node_bot y :: combine_prod f [] ys'

  let gram_lift (f : node -> node -> node) (g1 : gram) (g2 : gram) : gram =
    if g1 == g2 then g1
    else
      Gram.fold
        (fun sym q acc ->
          Gram.update sym
            (function
              | None -> Some (combine_prod f [] q)
              | Some p ->
                  let r = combine_prod f p q in
                  if r == p then Some p else Some r)
            acc)
        g2 g1

  let gram_join : gram -> gram -> gram = gram_lift node_join
  let gram_widen : gram -> gram -> gram = gram_lift node_widen

  let bottom : t = { root = node_bot; gram = Gram.empty }

  let is_bottom (v : t) : bool =
    v.root.ai = ABot && SymSet.is_empty v.root.syms

  let rec prod_leq (xs : node list) (ys : node list) : bool =
    match (xs, ys) with
    | [], [] -> true
    | x :: xs', y :: ys' -> node_leq x y && prod_leq xs' ys'
    | x :: xs', [] -> node_leq x node_bot && prod_leq xs' []
    | [], y :: ys' -> node_leq node_bot y && prod_leq [] ys'

  let leq (a : t) (b : t) : bool =
    if a == b then true
    else if is_bottom a then true
    else
      node_leq a.root b.root
      && (a.gram == b.gram
         || Gram.for_all
              (fun s pa ->
                let pb =
                  match Gram.find_opt s b.gram with Some p -> p | None -> []
                in
                prod_leq pa pb)
              a.gram)

  let join (a : t) (b : t) : t =
    if a == b then a
    else if is_bottom a then b
    else if is_bottom b then a
    else { root = node_join a.root b.root; gram = gram_join a.gram b.gram }

  let widen (a : t) (b : t) : t =
    if a == b then a
    else if is_bottom a then b
    else if is_bottom b then a
    else { root = node_widen a.root b.root; gram = gram_widen a.gram b.gram }

  (** {1 Construction / abstraction} *)

  let int_lit (n : int) : t =
    { root = { ai = AFin (IntSet.singleton n); syms = SymSet.empty };
      gram = Gram.empty }

  let of_aint (a : aint) : t =
    { root = { ai = a; syms = SymSet.empty }; gram = Gram.empty }

  (** {1 Role-annotated integer operators (§[sec:posdisamb])}

      The domain's one graded {!aint} carries every integer role; these thin
      wrappers make the role at each use site explicit, mirroring the paper's
      [==_{var,var}] vs [==_{num,num}] annotations. *)

  (** [int(α_r{n})]: inject a constant into the base domain of role [r]. Every
      role injects a literal as the exact singleton — the role distinction is in
      how {e joins} coarsen it: the key roles never grow (the routing below keeps
      them singletons), whereas the numeric role may widen in its base domain. *)
  let int_of_role (_r : Role.t) (n : int) : aint = AFin (IntSet.singleton n)

  (** [==_{r,r ⇒ bool}] on identifiers: whether the routed key constant [c] is
      among the requested key [k]. Used for the [lookup] ([r = var]) and [fundef]
      ([r = fname]) comparisons; exact because both sides are singleton-exact. *)
  let key_eq (_key_role : Role.t) (c : int) (k : aint) : bool =
    Domain_rtg.aint_mem c k

  (** The [==_{num,num}] / arithmetic operators of the numeric base domain. *)
  let num_binop (op : Domain_rtg.binop) (a : aint) (b : aint) : aint =
    Domain_rtg.aint_binop op a b

  (** Split a key argument's abstract integer over the collected set [c_p] into
      the collected candidate keys (each routed to its own symbol) and the
      residual — the part concretizing outside [c_p] (the paper's [★] block),
      over-approximated by the argument's own abstract integer. *)
  let split_key (c_p : IntSet.t) (key : aint) : int list * aint option =
    match key with
    | ABot -> ([], None)
    | AFin s ->
        let coll = IntSet.inter s c_p in
        let rest = IntSet.diff s c_p in
        ( IntSet.elements coll,
          if IntSet.is_empty rest then None else Some (AFin rest) )
    | AItv (lo, hi) ->
        (* every collected constant inside the interval is a candidate; the
           interval itself stands for the (possible) residual *)
        ( IntSet.elements (IntSet.filter (fun c -> lo <= c && c <= hi) c_p),
          Some key )
    | ATop -> (IntSet.elements c_p, Some ATop)

  (** Constructor formation: route on the first (key) argument and pin the routed
      symbol's key field to its block — the paper's [meet of tag# with G_max].
      The non-key fields are the argument root nodes; the grammar is the join of
      the argument grammars plus the routed productions, an existing production
      of the same symbol joining field-wise as in the base tree-grammar domain. *)
  let tag (_site : site) (tg : S_syntax.tag) (args : t list) : t =
    let merged =
      List.fold_left (fun g (a : t) -> gram_join g a.gram) Gram.empty args
    in
    let add_prod (g : gram) (s : sym) (prod : node list) : gram =
      Gram.update s
        (function
          | None -> Some prod
          | Some existing -> Some (combine_prod node_join existing prod))
        g
    in
    (* the routed (symbol, production) pairs of a keyed construction, on the
       integer-key field of role [key_role] (§[sec:posdisamb]) *)
    let keyed (key_role : Role.t) (c_p : IntSet.t) (mk : int -> sym) (key : t)
        (rest : t list) : (sym * node list) list =
      let coll, resid = split_key c_p key.root.ai in
      let rest_nodes = List.map (fun (a : t) -> a.root) rest in
      let routed =
        List.map
          (fun c ->
            ( mk c,
              { ai = int_of_role key_role c; syms = SymSet.empty } :: rest_nodes
            ))
          coll
      in
      (* trees (or residual ints) in the key position belong to the garbage
         block; carry the key's symbols there so the cover stays total *)
      let garb_key_ai = match resid with Some a -> a | None -> ABot in
      if resid = None && SymSet.is_empty key.root.syms then routed
      else
        (SGarb tg, { ai = garb_key_ai; syms = key.root.syms } :: rest_nodes)
        :: routed
    in
    (* the program-derived key block and symbol constructor for the integer-key
       role the map puts on this constructor's key field: [env]/[defs] conses key
       by binder / function name, an exp node by its own-tag label *)
    let key_spec (role : Role.t) : (IntSet.t * (int -> sym)) option =
      match role with
      | Role.Var -> Some (var_p, fun c -> SVar c)
      | Role.Fname -> Some (fun_p, fun c -> SFun c)
      | Role.Label ->
          let lab_tg =
            match Hashtbl.find_opt labs_by_tag tg with
            | Some s -> s
            | None -> IntSet.empty
          in
          Some (lab_tg, fun l -> SExp l)
      | _ -> None
    in
    let garbage () = [ (SGarb tg, List.map (fun (a : t) -> a.root) args) ] in
    let prods : (sym * node list) list =
      match (Role.fields tg, args) with
      (* a keyed construction: route on its integer-key field (field 0, whose
         role the map designates as an identifier key) *)
      | Some (key_role :: _), key :: rest when Role.is_key key_role -> (
          match key_spec key_role with
          | Some (c_p, mk) -> keyed key_role c_p mk key rest
          | None -> garbage ())
      (* the program wrapper [Prog(defs, main)] — an ADT-keyed pair *)
      | Some [ Role.Fundef; Role.Exp ], [ defs; main ]
        when String.equal tg T.tag_prog ->
          [ (SProg, [ defs.root; main.root ]) ]
      (* nullary reified constants: their own nullary symbol *)
      | Some [], [] ->
          if String.equal tg T.tag_eof then [ (SEof, []) ]
          else if String.equal tg T.tag_empty then [ (SEmpty, []) ]
          else if String.equal tg "True" then [ (STrue, []) ]
          else if String.equal tg "False" then [ (SFalse, []) ]
          else garbage ()
      | _ ->
          (* a construction outside the T encoding (junk flows): the tag's
             garbage block, fields stored as-is — total and sound *)
          garbage ()
    in
    let gram = List.fold_left (fun g (s, p) -> add_prod g s p) merged prods in
    let syms =
      List.fold_left (fun s (sym, _) -> SymSet.add sym s) SymSet.empty prods
    in
    { root = { ai = ABot; syms }; gram }

  (** {1 Primitives (same numeric arithmetic as the base domain)} *)

  let bool_true : t =
    { root = { ai = ABot; syms = SymSet.singleton STrue };
      gram = Gram.singleton STrue [] }

  let bool_false : t =
    { root = { ai = ABot; syms = SymSet.singleton SFalse };
      gram = Gram.singleton SFalse [] }

  (* The interpreter's primitives are the role-annotated operators of
     §[sec:posdisamb]: arithmetic in [ℤ^ABS_num], and the equality tests [eq] and
     [iszero]. [eq] carries the paper's role annotation implicitly — the graded
     {!aint} is shared by every integer role, so one transfer serves the numeric
     [==_{num,num}] of [Ifz] and the singleton-exact key comparisons
     [==_{var,var}] / [==_{fname,fname}] of [lookup] / [fundef] alike. (Inside an
     auxiliary {e denotation}, where the spine is walked abstractly rather than
     stepped, the same comparison is {!key_eq}.) *)
  let prim (o : S_syntax.prim) (args : t list) : t option =
    match (o, args) with
    | "add", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (num_binop Domain_rtg.BAdd a.root.ai b.root.ai))
    | "sub", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (num_binop Domain_rtg.BSub a.root.ai b.root.ai))
    | "mul", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (num_binop Domain_rtg.BMul a.root.ai b.root.ai))
    (* div / mod / lt: numeric-role transfers reusing the base domain's sound
       operators, since the numeric role shares its graded {!aint}. *)
    | "div", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (Domain_rtg.aint_div a.root.ai b.root.ai))
    | "mod", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (Domain_rtg.aint_mod a.root.ai b.root.ai))
    | "lt", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else Some (of_aint (Domain_rtg.aint_lt a.root.ai b.root.ai))
    | "eq", [ a; b ] ->
        if a.root.ai = ABot || b.root.ai = ABot then None
        else
          let x = a.root.ai and y = b.root.ai in
          let may_eq =
            match (x, y) with
            | ATop, _ | _, ATop -> true
            | AFin s, AFin t -> not (IntSet.is_empty (IntSet.inter s t))
            | _ ->
                let l1, h1 = Domain_rtg.range x
                and l2, h2 = Domain_rtg.range y in
                max l1 l2 <= min h1 h2
          in
          let may_neq =
            match
              (Domain_rtg.aint_the_point x, Domain_rtg.aint_the_point y)
            with
            | Some m, Some n -> m <> n
            | _ -> true
          in
          let t = if may_eq then bool_true else bottom in
          let f = if may_neq then bool_false else bottom in
          let r = join t f in
          if is_bottom r then None else Some r
    | "iszero", [ a ] ->
        if a.root.ai = ABot then None
        else
          let mz = Domain_rtg.aint_mem 0 a.root.ai in
          let mnz =
            match a.root.ai with
            | ABot -> false
            | ATop -> true
            | AFin s -> IntSet.exists (fun n -> n <> 0) s
            | AItv (lo, hi) -> not (lo = 0 && hi = 0)
          in
          let t = if mz then bool_true else bottom in
          let f = if mnz then bool_false else bottom in
          let r = join t f in
          if is_bottom r then None else Some r
    | _ -> None

  (** {1 Inspection} *)

  let has_tag (tg : S_syntax.tag) (v : t) : bool =
    SymSet.exists (fun s -> String.equal (sym_tag s) tg) v.root.syms

  (** Per-{e symbol} field tuples — the key and the payload stay relationally
      paired per routed key, which is what makes the analyzed [lookup]/[fundef]
      comparisons exact. *)
  let fields (tg : S_syntax.tag) (arity : int) (v : t) : t list list option =
    let tuples =
      SymSet.fold
        (fun s acc ->
          if String.equal (sym_tag s) tg then
            match Gram.find_opt s v.gram with
            | Some prod when List.length prod = arity ->
                List.map (fun fn -> { root = fn; gram = v.gram }) prod :: acc
            | _ -> acc
          else acc)
        v.root.syms []
    in
    match tuples with [] -> None | _ -> Some tuples

  let root_int (v : t) : aint = v.root.ai

  (** {1 Grammar GC (γ-preserving reachability restriction)} *)

  let reachable_syms (g : gram) (roots : SymSet.t) : SymSet.t =
    let rec loop seen frontier =
      match frontier with
      | [] -> seen
      | s :: rest -> (
          match Gram.find_opt s g with
          | None -> loop seen rest
          | Some prod ->
              let seen', frontier' =
                List.fold_left
                  (fun (seen, fr) (n : node) ->
                    SymSet.fold
                      (fun s2 (seen, fr) ->
                        if SymSet.mem s2 seen then (seen, fr)
                        else (SymSet.add s2 seen, s2 :: fr))
                      n.syms (seen, fr))
                  (seen, rest) prod
              in
              loop seen' frontier')
    in
    loop roots (SymSet.elements roots)

  let gc (v : t) : t =
    if Gram.is_empty v.gram then v
    else
      let keep = reachable_syms v.gram v.root.syms in
      if Gram.for_all (fun s _ -> SymSet.mem s keep) v.gram then v
      else { v with gram = Gram.filter (fun s _ -> SymSet.mem s keep) v.gram }

  (** {1 Concretization membership (tests' soundness oracle)} *)

  let rec mem (c : S_cek.value) (v : t) : bool =
    match c with
    | S_cek.VInt n -> Domain_rtg.aint_mem n v.root.ai
    | S_cek.VTag (t, vs) ->
        SymSet.exists
          (fun s ->
            String.equal (sym_tag s) t
            &&
            match Gram.find_opt s v.gram with
            | None -> false
            | Some prod ->
                List.length prod = List.length vs
                && List.for_all2
                     (fun fn ci -> mem ci { root = fn; gram = v.gram })
                     prod vs)
          v.root.syms

  (** {1 The abstracted program value}

      The encoded program abstracts through {!tag} itself: every node routes to
      its keyed symbol with an exact singleton key, so the result is the
      program-derived grammar at maximal precision — the [G_max]-shaped value the
      fixpoint starts from. *)
  let abstract_value (v : S_cek.value) : t =
    let rec go (v : S_cek.value) : t =
      match v with
      | S_cek.VInt n -> int_lit n
      | S_cek.VTag (t, vs) -> tag External t (List.map go vs)
    in
    go v

  let prog_value () : t = abstract_value (T.enc_program P.prog)

  (** {1 Specialized abstract auxiliary denotations}

      The paper's [A⟦lookup⟧] / [A⟦fundef⟧] / [A⟦extend⟧] lifted to this domain,
      for engines that fold the auxiliary macro steps instead of analyzing the
      auxiliary bodies; [None] means the concrete run is stuck, so there is
      nothing to cover. [lookup] and [fundef] walk the {e grammar spine} — the
      cons symbols reachable from the root through the tail field, each visited
      once. The keyed cover abstracts the spine order away, so every key that
      {e may} match contributes its slot: joined keys degrade to a union over the
      candidates, never to ⊤. *)

  let spine_walk (v : t) ~(cons_tag : S_syntax.tag)
      ~(matches : sym -> aint -> bool) (key : aint) : t =
    let rec loop (visited : SymSet.t) (frontier : sym list) (acc : t) : t =
      match frontier with
      | [] -> acc
      | s :: rest ->
          if SymSet.mem s visited then loop visited rest acc
          else
            let visited = SymSet.add s visited in
            if not (String.equal (sym_tag s) cons_tag) then
              loop visited rest acc
            else (
              match Gram.find_opt s v.gram with
              | Some [ _k; payload; tail ] ->
                  let acc =
                    if matches s key then
                      join acc { root = payload; gram = v.gram }
                    else acc
                  in
                  loop visited (SymSet.elements tail.syms @ rest) acc
              | _ -> loop visited rest acc)
    in
    loop SymSet.empty (SymSet.elements v.root.syms) bottom

  let aux_denot (fname : string) (args : t list) : t option =
    (* the ★ block matches only a key with a residual outside the collected
       set (a collected key can never equal a garbage node's key) *)
    let has_residual (c_p : IntSet.t) (key : aint) : bool =
      snd (split_key c_p key) <> None
    in
    if String.equal fname Interp_st.f_lookup then
      match args with
      | [ e; x ] ->
          let r =
            spine_walk e ~cons_tag:T.tag_extend
              ~matches:(fun s key ->
                match s with
                | SVar c -> key_eq Role.Var c key (* [==_{var,var}] *)
                | SGarb _ -> has_residual var_p key
                | _ -> false)
              x.root.ai
          in
          if is_bottom r then None else Some r
      | _ -> None
    else if String.equal fname Interp_st.f_fundef then
      match args with
      | [ d; f ] ->
          let r =
            spine_walk d ~cons_tag:T.tag_fun
              ~matches:(fun s key ->
                match s with
                | SFun c -> key_eq Role.Fname c key (* [==_{fname,fname}] *)
                | SGarb _ -> has_residual fun_p key
                | _ -> false)
              f.root.ai
          in
          if is_bottom r then None else Some r
      | _ -> None
    else if String.equal fname Interp_st.f_extend then
      match args with
      | [ e; x; v ] -> Some (tag External T.tag_extend [ x; v; e ])
      | _ -> None
    else None
end
