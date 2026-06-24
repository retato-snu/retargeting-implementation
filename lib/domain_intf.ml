(** Value-domain interface that {!S_abstract.Make} is parameterized over. *)

module IntSet = Set.Make (Int)

(* Abstract-integer lattice (paper A1): [⊥], a finite exact set, or [⊤]. *)
type aint = ABot | AFin of IntSet.t | ATop

type site = Internal of Label.t | External

module type DOMAIN = sig
  type nonrec aint = aint = ABot | AFin of IntSet.t | ATop

  val aint_mem : int -> aint -> bool

  type nonrec site = site = Internal of Label.t | External

  type t

  val bottom : t
  val is_bottom : t -> bool
  val leq : t -> t -> bool
  val join : t -> t -> t
  val widen : t -> t -> t

  val int_lit : int -> t
  val tag : site -> S_syntax.tag -> t list -> t
  val prim : S_syntax.prim -> t list -> t option

  val has_tag : S_syntax.tag -> t -> bool

  (* Per-site field tuples for a tag, or [None]; pure projection, no grammar GC. *)
  val fields : S_syntax.tag -> int -> t -> t list list option

  val root_int : t -> aint

  (* γ-preserving GC: result denotes the same language as input (main.tex l.1532); identity up to γ. *)
  val gc : t -> t
end
