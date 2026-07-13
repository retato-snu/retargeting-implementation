(** The value-domain interface the partitioned abstract interpreter
    ({!S_abstract.Make}) is parameterized over: every operation the analyzer
    performs on abstract values flows through this one signature, so the value
    domain is a swappable parameter. The default instantiation is {!Domain_rtg},
    re-exported via [include Make (Domain_rtg)], which leaves the public
    {!S_abstract} API unchanged.

    The signature exposes exactly the surface the analyzer core uses, including
    the {e concrete} shapes it pattern-matches on: the abstract-integer lattice
    [aint] (paper A1, a single ℘(Int)-with-top) and the allocation [site]. Keeping
    those manifest lets the core's exact-label extraction ([root_int] / [AFin]
    folding) and site construction ([Internal l]) stay structurally identical to
    the pre-functor code. Under the non-flambda toolchain these ops dispatch
    through a runtime module record instead of being inlined, so the in-process
    analyzer pays a small dispatch cost; the generated stored analyzer names
    {!Domain_rtg} directly and is unaffected. *)

module IntSet = Set.Make (Int)

(** The graded abstract-integer lattice (paper "Domain disambiguation"): [⊥]; an
    {e exact} finite set [AFin s], kept while small, so that code locations,
    variable ids and fun ids — drawn from the finite program space — stay exact,
    which T-flow sensitivity needs; an interval [AItv (lo, hi)], to which a
    position escapes once it grows past the cardinality bound; or [⊤]. Defined
    here rather than only inside [DOMAIN] so the concrete {!Domain_rtg} can
    re-export this very type and thus match the signature nominally. *)
type aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

(** Allocation site: an internal program label, optionally refined by the
    {e decoded T context} of the allocating index, or the external site. The
    refinement is legal because the paper's [Sym] is an arbitrary finite
    tag-mapped set, so [site × T-context] symbol families are an instantiation of
    it; they retarget the {e value domain}'s sensitivity the way the partition
    index retargets the control's. *)
type site =
  | Internal of Label.t
  | InternalT of Label.t * Label.t list
      (** site refined by the sorted decoded-T-context labels *)
  | External

module type DOMAIN = sig
  type nonrec aint = aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

  val aint_mem : int -> aint -> bool

  type nonrec site = site =
    | Internal of Label.t
    | InternalT of Label.t * Label.t list
    | External

  (** Abstract values. *)
  type t

  (** {1 Lattice} *)

  val bottom : t
  val is_bottom : t -> bool
  val leq : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t

  (** {1 Construction / abstraction} *)

  val int_lit : int -> t
  val tag : site -> S_syntax.tag -> t list -> t
  val prim : S_syntax.prim -> t list -> t option

  (** {1 Inspection} *)

  val has_tag : S_syntax.tag -> t -> bool

  (** Per-site field tuples for a tag, or [None] if the value cannot carry it.
      A pure projection — no grammar GC. *)
  val fields : S_syntax.tag -> int -> t -> t list list option

  (** The root abstract integer (used for exact T-label extraction). *)
  val root_int : t -> aint

  (** {1 Garbage collection (γ-preserving)}

      [gc v] denotes the {e same language} as [v] (mutual [leq]) with a minimal
      stored representation — for the tree-grammar domain, the grammar restricted
      to the symbols reachable from the root (the paper's "the grammar component
      of each field value can be garbage collected"). Being the identity up to γ,
      it never changes a result; the analyzer applies it to the field values it
      {e stores} (the abstract-[Match] successor environments) to keep stored
      grammars compact. A domain with no useful GC returns its input unchanged. *)
  val gc : t -> t
end
