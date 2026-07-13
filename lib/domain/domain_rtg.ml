(** Tree-grammar abstraction of S values: the abstract value domain [Val#],
    abstracting sets of concrete values [S_cek.value = VInt of int | VTag of tag
    * value list] following the paper's "Tree Grammar Abstraction of Values".

    Three layers, as in the paper: a {b node} [w = <n#, S>] pairs an abstract
    integer with a symbol set [S ⊆ Sym]; a {b grammar} [G = [S |-> <w1..wk>]] maps
    each symbol to the field-node tuple of its single production; an {b abstract
    value} [v# = <w, G>] is a root node plus a local grammar. Symbols are
    nonterminals, productions their right-hand sides, abstract integers the
    terminal leaves, and a node's symbol set a disjunction of nonterminals.

    The paper takes [Sym] to be any finite symbol set with a tag map
    [tag : Sym -> Tag]. We instantiate a symbol as an {b allocation site} — the S
    [LetTag] label that built the value — paired with the tag it allocates, plus a
    distinguished {!External} site for externally supplied values. Same tag at
    different sites therefore stays apart (e.g. distinct T sub-expressions encoded
    by the same [Sub] tag), which is the paper's recipe for relational
    distinctions: different symbols with the same tag, only non-relational
    properties inside a symbol. [G_max] is never materialised globally; each value
    carries only the productions reachable from its root. *)

(** {1 Abstract integers} *)

(* [IntSet], [aint] and [site] are declared once in {!Domain_intf} (the domain
   signature the analyzer core is functorized over) and re-exported here, so that
   [Domain_rtg] satisfies [Domain_intf.DOMAIN] with nominally-identical types. *)
module IntSet = Domain_intf.IntSet

(** An abstract integer: a graded powerset/interval lattice, γ being the obvious
    set of integers ([ABot] none, [AFin s] exactly [s], [AItv (lo,hi)] that
    range, [ATop] any). The grading is upward: a small position stays an exact
    [AFin] — so code locations / var ids / fun ids, drawn from the finite program
    space, stay exact, which T-flow needs — a numeric position outgrowing the
    cardinality bound escapes to [AItv], and an interval whose bounds keep growing
    escapes to [ATop]. Each escape loses precision but keeps chains finite. *)
type aint = Domain_intf.aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

(** Cardinality past which a finite set escapes to an interval. Id/label
    positions never reach it; numeric values can. *)
let fin_safety_bound = 4096

(** Cardinality past which {e widening} (not join) escapes a finite set to an
    interval. Widening runs only at fixpoint re-visits, where convergence must be
    fast: a numeric chain accreting one integer per iteration would otherwise take
    {!fin_safety_bound} iterations to escape. The bound stays well above the
    id/label space (a few dozen values per position in practice), so id/label
    positions still widen exactly. *)
let fin_widen_bound = 128

let aint_bot = ABot
let aint_top = ATop

(** The numeric [lo, hi] range of a non-bottom, non-top abstract integer. *)
let range : aint -> int * int = function
  | AFin s -> (IntSet.min_elt s, IntSet.max_elt s)
  | AItv (lo, hi) -> (lo, hi)
  | ABot | ATop -> invalid_arg "Domain_rtg.range"

(** {2 Constructors} *)

let aint_point (n : int) : aint = AFin (IntSet.singleton n)

(** Normalise: empty -> bottom, small -> exact [AFin], large -> [AItv]. *)
let aint_fin (s : IntSet.t) : aint =
  if IntSet.is_empty s then ABot
  else if IntSet.cardinal s <= fin_safety_bound then AFin s
  else AItv (IntSet.min_elt s, IntSet.max_elt s)

(** {2 Lattice operations} *)

let aint_leq (a : aint) (b : aint) : bool =
  match (a, b) with
  | ABot, _ -> true
  | _, ATop -> true
  | ATop, _ -> false
  | _, ABot -> false
  | AFin s, AFin t -> IntSet.subset s t
  | AFin s, AItv (lo, hi) ->
      let l, h = (IntSet.min_elt s, IntSet.max_elt s) in
      lo <= l && h <= hi
  | AItv (l, h), AItv (lo, hi) -> lo <= l && h <= hi
  | AItv _, AFin _ -> false

(** Join: set union while both sides are exact, interval hull once either has
    escaped, [ATop] absorbing. *)
let aint_join (a : aint) (b : aint) : aint =
  match (a, b) with
  | ABot, x | x, ABot -> x
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t -> aint_fin (IntSet.union s t)
  | _ ->
      let l1, h1 = range a and l2, h2 = range b in
      AItv (min l1 l2, max h1 h2)

(** [n ∈ γ a]. *)
let aint_mem (n : int) (a : aint) : bool =
  match a with
  | ABot -> false
  | ATop -> true
  | AFin s -> IntSet.mem n s
  | AItv (lo, hi) -> lo <= n && n <= hi

(** Widening. An [AFin] over the finite id/label space saturates and stays exact;
    past {!fin_widen_bound} a numeric position escapes to an [AItv], and an
    interval whose bounds keep growing escapes to [ATop]. Ascending chains are
    therefore finite: each position climbs at most exact -> interval -> top, and
    an interval only re-widens by strictly leaving its old bounds. *)
let aint_widen (a : aint) (b : aint) : aint =
  match (a, b) with
  | _, ABot -> a
  | ABot, x -> x
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t ->
      if IntSet.subset t s then a
      else
        let u = IntSet.union s t in
        if IntSet.cardinal u <= fin_widen_bound then AFin u
        else AItv (IntSet.min_elt u, IntSet.max_elt u)
  | AItv (l1, h1), _ ->
      let l2, h2 = range b in
      if l2 < l1 || h2 > h1 then ATop else a
  | AFin _, AItv _ ->
      let l1, h1 = range a and l2, h2 = range b in
      AItv (min l1 l2, max h1 h2)

(** {1 Symbols: allocation sites carrying their tag} *)

(** An allocation site: the S [LetTag] command label that built the value, or the
    distinguished [External] site of externally supplied / initial-input values. *)
type site = Domain_intf.site =
  | Internal of Label.t
  | InternalT of Label.t * Label.t list
  | External

let compare_site (a : site) (b : site) : int =
  match (a, b) with
  | External, External -> 0
  | External, _ -> -1
  | _, External -> 1
  | Internal x, Internal y -> Label.compare x y
  | Internal _, InternalT _ -> -1
  | InternalT _, Internal _ -> 1
  | InternalT (x, cx), InternalT (y, cy) ->
      let c = Label.compare x y in
      if c <> 0 then c else List.compare Label.compare cx cy

let string_of_site : site -> string = function
  | External -> "ext"
  | Internal l -> Label.to_string l
  | InternalT (l, ctx) ->
      Printf.sprintf "%s@{%s}" (Label.to_string l)
        (String.concat "," (List.map Label.to_string ctx))

(** A grammar symbol: an allocation site together with the tag it allocates.
    [tag] (the paper's [tag : Sym -> Tag]) reads the carried tag. *)
module Sym = struct
  type t = { site : site; tag : S_syntax.tag }

  let make site tag = { site; tag }
  let tag (s : t) : S_syntax.tag = s.tag

  let compare (a : t) (b : t) : int =
    let c = compare_site a.site b.site in
    if c <> 0 then c else String.compare a.tag b.tag

  let to_string (s : t) : string =
    Printf.sprintf "%s@%s" s.tag (string_of_site s.site)
end

module SymSet = Set.Make (Sym)
module Gram = Map.Make (Sym)

(** {1 Nodes, grammars, abstract values} *)

type node = { ai : aint; syms : SymSet.t }

(** Each symbol maps to the field-node tuple of its single production; a symbol
    absent from the grammar contributes no concrete trees. *)
type gram = node list Gram.t

type t = { root : node; gram : gram }

(** {1 Smart constructors and lattice on nodes / grammars}

    The encoded program is threaded through the analysis almost unchanged, so most
    combinations below reproduce one operand verbatim. The combiners detect that
    and return the {e physically existing} operand sub-structure instead of an
    identical copy — an allocation optimization only, but the physical equalities
    it preserves also let callers short-circuit whole traversals. *)

let node_bot : node = { ai = ABot; syms = SymSet.empty }

let node_leq (a : node) (b : node) : bool =
  aint_leq a.ai b.ai && SymSet.subset a.syms b.syms

let symset_union_share (s : SymSet.t) (t : SymSet.t) : SymSet.t =
  if s == t then s
  else if SymSet.is_empty t then s
  else if SymSet.is_empty s then t
  else if SymSet.subset t s then s
  else if SymSet.subset s t then t
  else SymSet.union s t

let node_join (a : node) (b : node) : node =
  if a == b then a
  else
    let ai = aint_join a.ai b.ai in
    let syms = symset_union_share a.syms b.syms in
    if ai == a.ai && syms == a.syms then a
    else if ai == b.ai && syms == b.syms then b
    else { ai; syms }

let node_widen (a : node) (b : node) : node =
  if a == b then a
  else
    let ai = aint_widen a.ai b.ai in
    let syms = symset_union_share a.syms b.syms in
    if ai == a.ai && syms == a.syms then a
    else if ai == b.ai && syms == b.syms then b
    else { ai; syms }

(** Pointwise combine of two productions. Both productions for one symbol have the
    same arity (fixed by the symbol's tag), so a length mismatch is a defensive
    case, handled by padding with [node_bot]. *)
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

(** Pointwise lift of a node combiner to grammars: a symbol present in only one
    grammar is combined against the missing (bottom) production, so
    [gram_lift node_join] is the grammar join. Folding [g2] into [g1] beats
    [Gram.merge], which reallocates every binding, because [Gram.update] rebuilds
    only the spine down to a key it changes; both combiners used here satisfy
    [combine_prod f p [] = p] and [combine_prod f [] q = q], so the result is the
    [Gram.merge] grammar binding for binding. *)
let gram_lift (f : node -> node -> node) (g1 : gram) (g2 : gram) : gram =
  if g1 == g2 then
    (* Both join and widen leave a production combined with itself unchanged. *)
    g1
  else
    Gram.fold
      (fun sym q acc ->
        Gram.update sym
          (function
            | None -> Some (combine_prod f [] q)
            | Some p ->
                let r = combine_prod f p q in
                (* Keep sharing so [Gram.update] reuses the existing subtree. *)
                if r == p then Some p else Some r)
          acc)
      g2 g1

let gram_join : gram -> gram -> gram = gram_lift node_join
let gram_widen : gram -> gram -> gram = gram_lift node_widen

(** {1 Lattice elements} *)

(** Empty root node and empty grammar; γ is the empty set. *)
let bottom : t = { root = node_bot; gram = Gram.empty }

(** Structurally bottom: a root with no integers and no symbols reaches no
    production, so its γ is empty whatever the grammar holds. *)
let is_bottom (v : t) : bool =
  v.root.ai = ABot && SymSet.is_empty v.root.syms

(** {1 Grammar garbage collection (γ-preserving)}

    A value's local grammar accumulates symbols it cannot reach, because [tag]
    joins in every argument's grammar and [fields] hands each projected field the
    whole parent grammar (the paper's [(w_i, G)]). [gc] restricts [G] to the least
    [R ⊇ w.syms] closed under "[S ∈ R] implies the symbols of every field of [G(S)]
    lie in [R]", yielding [<w, G|_R>].

    {b γ-preservation.} γ, and its decidable witnesses {!mem} and {!sample}, only
    ever consult [G(S)] for [S] reachable from the root: [mem] looks up a symbol of
    [w.syms] and recurses on each field node [<n_i#, S_i>] {e under the same
    grammar}, so its lookups are exactly the closure [R]. The two grammars thus
    agree on every symbol either side inspects and differ only on symbols neither
    inspects, giving [mem c <w,G> = mem c <w,G|_R>] for every concrete [c] and hence
    [γ<w,G> = γ<w,G|_R>]; the paper likewise makes it optional, a field value's
    grammar "can be garbage collected to eliminate unreachable symbols ... it is not
    essential for the soundness of the analysis." So [gc] preserves [leq], [join],
    [widen], [tag], [fields], [has_tag] and [mem] {e up to γ} — the criterion
    against a non-GC'd run is γ-equivalence (mutual [leq]), not equal
    representations — and, never enlarging a value nor touching a root, it leaves
    the ascending-chain argument intact. *)

(** The reachable set [R] above, as a worklist closure; each symbol expands once. *)
let reachable_syms (g : gram) (roots : SymSet.t) : SymSet.t =
  let rec loop (seen : SymSet.t) (frontier : Sym.t list) : SymSet.t =
    match frontier with
    | [] -> seen
    | s :: rest -> (
        match Gram.find_opt s g with
        | None -> loop seen rest
        | Some fields ->
            let seen', frontier' =
              List.fold_left
                (fun (seen, fr) (node : node) ->
                  SymSet.fold
                    (fun s2 (seen, fr) ->
                      if SymSet.mem s2 seen then (seen, fr)
                      else (SymSet.add s2 seen, s2 :: fr))
                    node.syms (seen, fr))
                (seen, rest) fields
            in
            loop seen' frontier')
  in
  loop roots (SymSet.elements roots)

(** Restrict [g] to [keep], returning [g] physically when nothing is dropped. *)
let restrict_gram (g : gram) (keep : SymSet.t) : gram =
  if Gram.for_all (fun s _ -> SymSet.mem s keep) g then g
  else Gram.filter (fun s _ -> SymSet.mem s keep) g

(** [gc v] restricts [v]'s grammar to the symbols reachable from its root, which
    is γ-preserving (above). Returns [v] physically when already minimal.

    {b Where it is applied.} Not in {!fields} (the paper's [fields#] is a pure
    projection) but in the [Match] consumers that {e store} what they project —
    [S_abstract.step_entry]'s [Match] arm and [Stage_runtime.project_branch] in the
    generated code — on each field value bound into an environment that enters the
    table: a [Match]-bound variable would otherwise carry the whole parent grammar,
    which is the dominant bloat and the only place GC pays off. The other [fields]
    consumer, [S_abstract.t_labels_of_value], keeps only field 0's abstract integer
    and discards the grammars, so it deliberately pays no GC. *)
let gc (v : t) : t =
  if Gram.is_empty v.gram then v
  else
    let keep = reachable_syms v.gram v.root.syms in
    let gram' = restrict_gram v.gram keep in
    if gram' == v.gram then v else { v with gram = gram' }

(** {1 Partial order} *)

(** Node-list comparison that treats absent fields as bottom. *)
let rec prod_leq (xs : node list) (ys : node list) : bool =
  match (xs, ys) with
  | [], [] -> true
  | x :: xs', y :: ys' -> node_leq x y && prod_leq xs' ys'
  | x :: xs', [] -> node_leq x node_bot && prod_leq xs' []
  | [], y :: ys' -> node_leq node_bot y && prod_leq [] ys'

(** [leq a b] holds iff [γ a ⊆ γ b]. Concretization is an order-embedding for
    well-formed values, so a structural comparison suffices: the root nodes, and
    the productions of every symbol. Symbols are canonical (a site/tag pair) and
    so shared by name, so grammars compare pointwise over the union of their
    domains, a missing production read as bottom. *)
let leq (a : t) (b : t) : bool =
  if a == b then true
  else if is_bottom a then true
  else
    node_leq a.root b.root
    &&
    (* A shared grammar makes every production identical, so the order reduces to
       the root comparison already checked. *)
    (a.gram == b.gram
    ||
    let doms =
      Gram.fold (fun s _ acc -> SymSet.add s acc)
        a.gram
        (Gram.fold (fun s _ acc -> SymSet.add s acc) b.gram SymSet.empty)
    in
    SymSet.for_all
      (fun s ->
        let pa = match Gram.find_opt s a.gram with Some p -> p | None -> [] in
        let pb = match Gram.find_opt s b.gram with Some p -> p | None -> [] in
        prod_leq pa pb)
      doms)

(** {1 Join} *)

(** Least upper bound: join the root nodes and the grammars pointwise. Symbols
    being canonical, there is nothing to rename; unreachable productions never
    contribute to γ. *)
let join (a : t) (b : t) : t =
  if a == b then a
  else if is_bottom a then b
  else if is_bottom b then a
  else { root = node_join a.root b.root; gram = gram_join a.gram b.gram }

(** {1 Widening}

    Termination. Symbol sets and grammar domains range over the finite site × tag
    space with arities fixed by the tag (no [G_max] is materialized: finiteness of
    this representation replaces the paper's [G ⊑ G_max] argument), so the grammar
    structure can grow only finitely, and each integer position is widened by
    {!aint_widen}, which stabilises after at most exact -> interval -> top. Every
    ascending chain therefore converges. *)
let widen (a : t) (b : t) : t =
  if a == b then a
  else if is_bottom a then b
  else if is_bottom b then a
  else { root = node_widen a.root b.root; gram = gram_widen a.gram b.gram }

(** {1 Concretization and membership}

    γ is the language of the grammar, infinite whenever the grammar is recursive,
    so in its place we expose a decidable membership test and a finite bounded
    [sample], both usable for soundness testing. *)

(** [mem v a] decides [v ∈ γ a]: an integer is a member iff the root node's
    abstract integer holds it; a tree [T(v1..vk)] is a member iff the root's symbol
    set holds some [S] with [tag(S) = T] whose production [G(S)] has arity [k] and
    each field [vi] is recursively a member of [<wi, G>]. *)
let rec mem (v : S_cek.value) (a : t) : bool =
  match v with
  | S_cek.VInt n -> aint_mem n a.root.ai
  | S_cek.VTag (t, vs) ->
      SymSet.exists
        (fun s ->
          String.equal (Sym.tag s) t
          &&
          match Gram.find_opt s a.gram with
          | None -> false
          | Some fields ->
              List.length fields = List.length vs
              && List.for_all2
                   (fun field vi -> mem vi { root = field; gram = a.gram })
                   fields vs)
        a.root.syms

(** A finite under-approximation of γ: the members of construction depth at most
    [depth]. Everything it returns satisfies [mem], but it is not complete (deeper
    trees are omitted, and [ATop] yields only a couple of witnesses). *)
let sample ?(depth = 3) (a : t) : S_cek.value list =
  let int_witnesses (ai : aint) : S_cek.value list =
    match ai with
    | ABot -> []
    | AFin s -> IntSet.fold (fun n acc -> S_cek.VInt n :: acc) s []
    | AItv (lo, hi) -> [ S_cek.VInt lo; S_cek.VInt hi ]
    | ATop -> [ S_cek.VInt 0; S_cek.VInt 1 ]
  in
  let rec go d node g : S_cek.value list =
    let ints = int_witnesses node.ai in
    let trees =
      if d <= 0 then []
      else
        SymSet.fold
          (fun s acc ->
            match Gram.find_opt s g with
            | None -> acc
            | Some fields ->
                let field_choices = List.map (fun f -> go (d - 1) f g) fields in
                if List.exists (fun c -> c = []) field_choices then acc
                else
                  let combos =
                    List.fold_right
                      (fun choices rest ->
                        List.concat_map
                          (fun c -> List.map (fun r -> c :: r) rest)
                          choices)
                      field_choices [ [] ]
                  in
                  List.map (fun args -> S_cek.VTag (Sym.tag s, args)) combos @ acc)
          node.syms []
    in
    ints @ trees
  in
  go depth a.root a.gram

(** {1 Abstract operations required by the analysis}

    The paper's [int#], [tag#_T], [fields#_T], plus the primitive abstractions the
    transfers need. *)

(** Integer injection [int#]: a leaf carrying the abstract integer at the root,
    with no symbols and an empty grammar. *)
let int_lit (n : int) : t =
  { root = { ai = aint_point n; syms = SymSet.empty }; gram = Gram.empty }

let any_int : t =
  { root = { ai = ATop; syms = SymSet.empty }; gram = Gram.empty }

(** Constructor formation at an allocation [site] (the paper's [tag#_T]): the root
    is the single symbol [<site, t>], its production the tuple of argument root
    nodes, and the grammar the join [⊔_i G_i] of the argument grammars carrying
    that production for [sym]. The new production is {b joined} (the paper's [⊔])
    with any production already bound to [sym], not overwritten: when a value built
    at the {e same} site flows back in as an argument (a recursive same-site
    constructor such as [C(C(1))]), [sym]'s base-case production is already in
    [merged_gram] and must survive. Sound: any [T(v1..vk)] with [vi ∈ γ(arg_i)] is
    a member of the result, since the symbol is at the root, the joined production
    over-approximates the argument root nodes, and the grammar join preserves each
    argument's productions. *)
let tag (site : site) (t : S_syntax.tag) (args : t list) : t =
  let arg_roots = List.map (fun a -> a.root) args in
  let merged_gram =
    List.fold_left (fun g a -> gram_join g a.gram) Gram.empty args
  in
  let sym = Sym.make site t in
  let gram =
    match Gram.find_opt sym merged_gram with
    | Some existing when List.length existing = List.length arg_roots ->
        (* Same-site recursive value: field-wise join the existing base-case
           production with the new arg roots (the paper's [⊔]). *)
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | Some existing ->
        (* Arity mismatch cannot occur for a real site; [combine_prod] pads with
           [node_bot], so the join still subsumes both productions. *)
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | None -> Gram.add sym arg_roots merged_gram
  in
  (* No [gc] here: [sym]'s production is exactly the argument root nodes, so every
     symbol of a minimal argument grammar stays reachable and the merge rewrites
     only [sym]'s own production. GC would shrink nothing. *)
  { root = { ai = ABot; syms = SymSet.singleton sym }; gram }

(** [tag#] at the external site, for seed values not built by a program [LetTag]. *)
let tag_external (t : S_syntax.tag) (args : t list) : t = tag External t args

(** Constructor-field projection [fields#_T], the paper's {b set of tuples}

    {[ {⟨(w_i, G)⟩ | S ∈ {S̄}, tag(S) = t, G(S) = ⟨w̄_i⟩} ]}

    realised as an outer list of one tuple per site-symbol [S] of tag [t] at the
    root whose production has the requested arity; each tuple's fields carry the
    {e shared} parent grammar (the paper's per-field [(w_i, G)]). Distinct sites of
    the same tag thus stay separate tuples — there is no cross-site field-wise
    join — so abstract [Match] can branch existentially over
    [⟨v̄_i⟩ ∈ fields#_T(...)] ([AbsMatch]) and keep per-site fields relationally
    paired; the {e same-site} join already happened upstream in [tag#]. [None] when
    no symbol of tag [t] with a production of that arity is possible at the root,
    which is the strictness callers rely on. Like the paper's [fields#] this is a
    pure projection: no grammar GC here (see {!gc} for where it happens). *)
let fields (t : S_syntax.tag) (arity : int) (a : t) : t list list option =
  let tuples =
    SymSet.fold
      (fun s acc ->
        if String.equal (Sym.tag s) t then
          match Gram.find_opt s a.gram with
          | Some field_nodes when List.length field_nodes = arity ->
              List.map (fun fn -> { root = fn; gram = a.gram }) field_nodes :: acc
          | _ -> acc
        else acc)
      a.root.syms []
  in
  match tuples with [] -> None | _ -> Some tuples

(** Whether some value in [γ a] is headed by tag [t]. Used by abstract [Match]. *)
let has_tag (t : S_syntax.tag) (a : t) : bool =
  SymSet.exists (fun s -> String.equal (Sym.tag s) t) a.root.syms

let has_int (a : t) : bool = a.root.ai <> ABot

(** {2 Primitive abstractions}

    Sound abstractions of the S primitives, consistent with [S_cek.eval_prim]; the
    paper leaves the primitive interpretation [O[o]#] a parameter. *)

let root_int (a : t) : aint = a.root.ai

(** Named rather than passed as a bare [int -> int -> int] so that the interval
    path below can reason about overflow per operation. *)
type binop = BAdd | BSub | BMul

let binop_fun : binop -> int -> int -> int = function
  | BAdd -> ( + )
  | BSub -> ( - )
  | BMul -> ( * )

(** Overflow-checked corner arithmetic for the interval path: [None] means the
    native (wrapping) operation may not equal the mathematical result. Native
    63-bit two's-complement facts used:
    - [a + b] can only overflow when the operand signs agree, and then the
      result's sign flips away from theirs;
    - [a - b] can only overflow when the operand signs differ, and then the
      result's sign flips away from [a]'s;
    - [a * b] (operands not 0/1/min_int) overflowed iff the division check
      [r / b <> a] fails — a wrapped [r = ab - k·2^63 (k≠0)] cannot pass it,
      since [|k·2^63 / b| ≥ 2] for any representable [b]. *)
let checked_add (a : int) (b : int) : int option =
  let r = a + b in
  if (a >= 0) = (b >= 0) && (r >= 0) <> (a >= 0) then None else Some r

let checked_sub (a : int) (b : int) : int option =
  let r = a - b in
  if (a >= 0) <> (b >= 0) && (r >= 0) <> (a >= 0) then None else Some r

let checked_mul (a : int) (b : int) : int option =
  if a = 0 || b = 0 then Some 0
  else if a = 1 then Some b
  else if b = 1 then Some a
  else if a = min_int || b = min_int then None
  else
    let r = a * b in
    if r / b = a then Some r else None

(** Lift a concrete binary integer op to abstract integers. On two finite sets the
    result is the set of all pairwise images (escaping to an interval past the
    bound), computed with the {e native, wrapping} op and so bit-exact with what
    the concrete machines ({!S_cek.eval_prim}'s [( - )] / [( * )], and the T
    machine) compute: exact, a fortiori sound. [ATop] absorbs, [ABot] propagates.

    With an interval operand the extremal-corner rule (valid for add, sub and mul)
    gives the hull, but only in unbounded arithmetic: the native ops wrap, and a
    wrapped corner yields an interval that {e excludes} genuinely reachable results
    — a real unsoundness. Any potentially overflowing corner therefore forfeits the
    hull argument and the result is [ATop]. When all four checked corners are
    overflow-free so is every interior image: add's and sub's interior results lie
    between the extreme corners, and mul's interior magnitudes are bounded by the
    largest corner magnitude. *)
let aint_binop (op : binop) (x : aint) (y : aint) : aint =
  match (x, y) with
  | ABot, _ | _, ABot -> ABot
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t ->
      let f = binop_fun op in
      let out =
        IntSet.fold
          (fun a acc -> IntSet.fold (fun b acc -> IntSet.add (f a b) acc) t acc)
          s IntSet.empty
      in
      aint_fin out
  | _ ->
      let checked =
        match op with
        | BAdd -> checked_add
        | BSub -> checked_sub
        | BMul -> checked_mul
      in
      let l1, h1 = range x and l2, h2 = range y in
      (match (checked l1 l2, checked l1 h2, checked h1 l2, checked h1 h2) with
      | Some a, Some b, Some c, Some d ->
          AItv (min (min a b) (min c d), max (max a b) (max c d))
      | _ -> ATop)

let aint_to_val (ai : aint) : t =
  { root = { ai; syms = SymSet.empty }; gram = Gram.empty }

let add (a : t) (b : t) : t =
  aint_to_val (aint_binop BAdd (root_int a) (root_int b))

let sub (a : t) (b : t) : t =
  aint_to_val (aint_binop BSub (root_int a) (root_int b))

let mul (a : t) (b : t) : t =
  aint_to_val (aint_binop BMul (root_int a) (root_int b))

(** {3 Division, remainder, order comparison: sound over-approximations of the
    total S primitives [div]/[mod]/[lt] of {!S_cek.eval_prim}} *)

(** [div]/[mod] on concrete integers, total ([_ / 0 = _ mod 0 = 0]) and {e identical}
    to {!S_cek.eval_prim}'s, so the finite-set paths below are bit-exact with the
    concrete machine and hence sound. *)
let safe_div (a : int) (b : int) : int = if b = 0 then 0 else a / b
let safe_mod (a : int) (b : int) : int = if b = 0 then 0 else a mod b

(** Elementwise image of a total binary op over two finite sets, via {!aint_fin}. *)
let aint_map2_fin (f : int -> int -> int) (s : IntSet.t) (t : IntSet.t) : aint =
  aint_fin
    (IntSet.fold
       (fun a acc -> IntSet.fold (fun b acc -> IntSet.add (f a b) acc) t acc)
       s IntSet.empty)

(** Abstract truncating division: exact elementwise on two finite sets. On a
    bounded dividend, truncated division is monotone in each argument over a
    sign-definite divisor sub-range, so the quotient extremes lie at the corners of
    the (dividend range) x (divisor sub-range) box; a divisor straddling 0 is split
    at 0 into its sign-definite parts, with the [div(_,0)=0] totality case folded
    in. An unbounded dividend, or a bound extreme enough to risk overflow, yields
    ⊤. Sound: the corner hull over-approximates every concrete quotient. *)
let aint_div (x : aint) (y : aint) : aint =
  match (x, y) with
  | ABot, _ | _, ABot -> ABot
  | AFin s, AFin t -> aint_map2_fin safe_div s t
  | ATop, _ -> ATop
  | _, ATop -> ATop (* n / top, including [n/0 = 0], is any integer *)
  | _ ->
      let l1, h1 = range x and l2, h2 = range y in
      if
        l1 <= min_int + 1 || h1 >= max_int - 1 || l2 <= min_int + 1
        || h2 >= max_int - 1
      then ATop
      else begin
        let cands = ref [] in
        let corners lo2 hi2 =
          List.iter
            (fun a ->
              List.iter (fun b -> cands := safe_div a b :: !cands) [ lo2; hi2 ])
            [ l1; h1 ]
        in
        if l2 >= 1 || h2 <= -1 then corners l2 h2 (* divisor sign-definite *)
        else begin
          (* straddles 0: split at 0, then add the div-by-0 => 0 case *)
          if l2 <= -1 then corners l2 (-1);
          if h2 >= 1 then corners 1 h2;
          cands := 0 :: !cands
        end;
        match !cands with
        | [] -> aint_point 0 (* divisor is exactly {0} *)
        | c :: rest ->
            let lo = List.fold_left min c rest
            and hi = List.fold_left max c rest in
            if lo = hi then aint_point lo else AItv (lo, hi)
      end

(** Abstract remainder: exact on two finite sets. Otherwise a bounded [b] bounds
    the result by [|b|-1] ([|a mod b| <= |b|-1] for [b<>0], and [mod(_,0)=0] lies
    inside that box), refined to a non-negative range when [a] is known
    non-negative, since native [mod] takes the sign of the dividend. A ⊤ [b] leaves
    the remainder unbounded; extreme interval bounds fall back to ⊤ to avoid
    [abs min_int] overflow. *)
let aint_mod (x : aint) (y : aint) : aint =
  match (x, y) with
  | ABot, _ | _, ABot -> ABot
  | AFin s, AFin t -> aint_map2_fin safe_mod s t
  | _, ATop -> ATop
  | _ ->
      let l2, h2 = range y in
      if l2 <= min_int + 1 || h2 >= max_int - 1 then ATop
      else
        let m = max (abs l2) (abs h2) in
        if m = 0 then aint_point 0 (* b is exactly {0}: remainder is 0 *)
        else
          let bound = m - 1 in
          let lo =
            match x with
            | AFin s when IntSet.min_elt s >= 0 -> 0
            | AItv (lx, _) when lx >= 0 -> 0
            | _ -> -bound
          in
          AItv (lo, bound)

(** Abstract order comparison [lt], valued in [{0,1}]. Decided when the operand
    ranges settle it ([a] entirely below / entirely at-or-above [b]), else [{0,1}]
    (the ⊤ of the two-point Boolean-as-int). Sound: the may-lt / may-ge tests use
    the range hull, which over-approximates the finite sets. *)
let aint_lt (x : aint) (y : aint) : aint =
  match (x, y) with
  | ABot, _ | _, ABot -> ABot
  | _ ->
      let may_lt, may_ge =
        match (x, y) with
        | ATop, _ | _, ATop -> (true, true)
        | _ ->
            let l1, h1 = range x and l2, h2 = range y in
            (l1 < h2, h1 >= l2)
      in
      let s = if may_lt then IntSet.singleton 1 else IntSet.empty in
      let s = if may_ge then IntSet.add 0 s else s in
      aint_fin s

let div (a : t) (b : t) : t = aint_to_val (aint_div (root_int a) (root_int b))

(** Named [modulo] because [mod] is an OCaml keyword. *)
let modulo (a : t) (b : t) : t =
  aint_to_val (aint_mod (root_int a) (root_int b))

let lt (a : t) (b : t) : t = aint_to_val (aint_lt (root_int a) (root_int b))

(** The Boolean values, nullary tags [True()]/[False()] exactly as
    [S_cek.eval_prim] builds them, at the external site since a primitive rather
    than a program [LetTag] produces them. *)
let abs_true : t = tag_external "True" []
let abs_false : t = tag_external "False" []

(** [True()] if [0] is possible, [False()] if a nonzero integer is, the join if
    both — so the concrete [iszero] image of every integer in [γ a] is covered. *)
let iszero (a : t) : t =
  let ai = root_int a in
  let may_zero = aint_mem 0 ai in
  let may_nonzero =
    match ai with
    | ABot -> false
    | ATop -> true
    | AFin s -> IntSet.exists (fun n -> n <> 0) s
    | AItv (lo, hi) -> not (lo = 0 && hi = 0)
  in
  let parts =
    (if may_zero then [ abs_true ] else [])
    @ if may_nonzero then [ abs_false ] else []
  in
  match parts with
  | [] -> bottom
  | x :: rest -> List.fold_left join x rest

(** The one value an abstract integer denotes, when it denotes exactly one. *)
let aint_the_point (x : aint) : int option =
  match x with
  | AFin s when IntSet.cardinal s = 1 -> Some (IntSet.choose s)
  | AItv (lo, hi) when lo = hi -> Some lo
  | _ -> None

(** [True()] if the two operands can be equal, [False()] if they can differ, the
    join if both — the paper's [==], used by the interpreter both on numbers
    ([==_num]) and on the identifier keys of [lookup] / [fundef] ([==_var],
    [==_fname]), which are singleton-exact and so decide it.

    Exactly as precise as the [iszero(a - b)] it replaces: on two finite sets both
    ask whether [0] is a pairwise difference, and on ranges [0 ∈ [l1-h2, h1-l2]]
    is precisely overlap. *)
let eq (a : t) (b : t) : t =
  let x = root_int a and y = root_int b in
  match (x, y) with
  | ABot, _ | _, ABot -> bottom
  | _ ->
      let may_eq =
        match (x, y) with
        | ATop, _ | _, ATop -> true
        | AFin s, AFin t -> not (IntSet.is_empty (IntSet.inter s t))
        | _ ->
            let l1, h1 = range x and l2, h2 = range y in
            max l1 l2 <= min h1 h2
      in
      let may_neq =
        match (aint_the_point x, aint_the_point y) with
        | Some m, Some n -> m <> n
        | _ -> true
      in
      let parts =
        (if may_eq then [ abs_true ] else [])
        @ if may_neq then [ abs_false ] else []
      in
      (match parts with
      | [] -> bottom
      | v :: rest -> List.fold_left join v rest)

(** Dispatch by name over [S_cek.eval_prim]'s operator set; [None] for an unknown
    primitive, so callers can raise the error the concrete machine would. *)
let prim (o : S_syntax.prim) (args : t list) : t option =
  match (o, args) with
  | "add", [ a; b ] -> Some (add a b)
  | "sub", [ a; b ] -> Some (sub a b)
  | "mul", [ a; b ] -> Some (mul a b)
  | "div", [ a; b ] -> Some (div a b)
  | "mod", [ a; b ] -> Some (modulo a b)
  | "lt", [ a; b ] -> Some (lt a b)
  | "eq", [ a; b ] -> Some (eq a b)
  | "iszero", [ a ] -> Some (iszero a)
  | _ -> None

(** {1 Specialized abstract auxiliary denotations (without domain
    disambiguation)}

    The paper's [A⟦lookup⟧] / [A⟦fundef⟧] / [A⟦extend⟧] lifted to this site-keyed
    tree-grammar domain (the disambiguated domain's counterpart is
    {!Domain_dis.Make.aux_denot}), for analyzers that apply an auxiliary as a single
    transfer rather than analyzing its body through the abstract S machine. [None]
    means every covered concrete run is stuck. [lookup] and [fundef] walk the
    value's {e grammar spine} — the cons-tagged symbols reachable from the root
    through the tail field, each visited once. The grammar abstracts away the
    concrete spine order, so no first-match cut is available and every cons whose
    key {e may} equal the requested id contributes its payload; their join is sound
    because the concrete walk returns exactly one of them. [extend] is the cons
    construction itself, attributed to the {e same} allocation site the analyzed
    [extend] body allocates at (extracted structurally from {!Interp_st.program}),
    so specialized and analyzed runs build compatible symbols. *)

(** [γ(a) ∩ γ(b) ≠ ∅]: may the two abstract integers denote a common integer? *)
let aint_may_eq (a : aint) (b : aint) : bool =
  match (a, b) with
  | ABot, _ | _, ABot -> false
  | ATop, _ | _, ATop -> true
  | AFin s, AFin t -> not (IntSet.is_empty (IntSet.inter s t))
  | AFin s, AItv (lo, hi) | AItv (lo, hi), AFin s ->
      IntSet.exists (fun n -> lo <= n && n <= hi) s
  | AItv (l1, h1), AItv (l2, h2) -> l1 <= h2 && l2 <= h1

(** Join of the payloads of every reachable [cons_tag] node whose key field may
    equal [key], following tail fields transitively; terminates because each
    grammar symbol is visited at most once. *)
let spine_lookup (v : t) ~(cons_tag : S_syntax.tag) (key : aint) : t =
  let rec loop (visited : SymSet.t) (frontier : Sym.t list) (acc : t) : t =
    match frontier with
    | [] -> acc
    | s :: rest ->
        if SymSet.mem s visited then loop visited rest acc
        else
          let visited = SymSet.add s visited in
          if not (String.equal (Sym.tag s) cons_tag) then loop visited rest acc
          else (
            match Gram.find_opt s v.gram with
            | Some [ k; payload; tail ] ->
                let acc =
                  if aint_may_eq k.ai key then
                    join acc { root = payload; gram = v.gram }
                  else acc
                in
                loop visited (SymSet.elements tail.syms @ rest) acc
            | _ -> loop visited rest acc)
  in
  loop SymSet.empty (SymSet.elements v.root.syms) bottom

(** The allocation site of the [Extend] cons in [extend]'s body, so that a
    specialized [extend] builds the {e same} symbol family the analyzed body does. *)
let extend_site : site Lazy.t =
  lazy
    (let found = ref External in
     (match
        List.find_opt
          (fun (d : S_syntax.fundef) ->
            String.equal d.S_syntax.name Interp_st.f_extend)
          Interp_st.program.S_syntax.funs
      with
     | None -> ()
     | Some d ->
         let rec scan (l : Label.t) : unit =
           match S_syntax.cmd_at Interp_st.program l with
           | S_syntax.Let (_, S_syntax.ETag (site, t, _), k)
             when String.equal t T_encoding.tag_extend ->
               found := Internal site;
               ignore k
           | S_syntax.Let (_, _, k) | S_syntax.LetCall (_, _, _, k) -> scan k
           | S_syntax.Match (_, branches) ->
               List.iter (fun (_, k) -> scan k) branches
           | S_syntax.Return _ -> ()
         in
         scan d.S_syntax.entry);
     !found)

let aux_denot (fname : string) (args : t list) : t option =
  if String.equal fname Interp_st.f_lookup then
    match args with
    | [ e; x ] ->
        let r = spine_lookup e ~cons_tag:T_encoding.tag_extend (root_int x) in
        if is_bottom r then None else Some (gc r)
    | _ -> None
  else if String.equal fname Interp_st.f_fundef then
    match args with
    | [ d; f ] ->
        let r = spine_lookup d ~cons_tag:T_encoding.tag_fun (root_int f) in
        if is_bottom r then None else Some (gc r)
    | _ -> None
  else if String.equal fname Interp_st.f_extend then
    match args with
    | [ e; x; v ] ->
        Some (tag (Lazy.force extend_site) T_encoding.tag_extend [ x; v; e ])
    | _ -> None
  else None

(** {1 Pretty-printing} *)

let string_of_aint (a : aint) : string =
  match a with
  | ABot -> "_|_"
  | ATop -> "Z"
  | AItv (lo, hi) -> Printf.sprintf "[%d,%d]" lo hi
  | AFin s ->
      "{" ^ String.concat "," (List.map string_of_int (IntSet.elements s)) ^ "}"

let string_of_node (w : node) : string =
  Printf.sprintf "<%s,{%s}>" (string_of_aint w.ai)
    (String.concat "," (List.map Sym.to_string (SymSet.elements w.syms)))

let to_string (v : t) : string =
  let prods =
    Gram.fold
      (fun s fields acc ->
        let rhs = String.concat "," (List.map string_of_node fields) in
        Printf.sprintf "%s->%s(%s)" (Sym.to_string s) (Sym.tag s) rhs :: acc)
      v.gram []
  in
  Printf.sprintf "(%s; [%s])" (string_of_node v.root)
    (String.concat "; " (List.rev prods))
