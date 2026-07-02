(** Value-domain interface for the partitioned abstract interpreter ({!S_abstract.Make}). *)

module IntSet = Set.Make (Int)

(** Abstract-integer lattice (paper "Domain disambiguation", l.2000): graded powerset/interval. *)
type aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

(** Allocation site: an internal program label or the external site. *)
type site = Internal of Label.t | External

module type DOMAIN = sig
  type nonrec aint = aint = ABot | AFin of IntSet.t | AItv of int * int | ATop

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

  val fields : S_syntax.tag -> int -> t -> t list list option

  val root_int : t -> aint

  (** γ-preserving GC: same denotation, minimal stored representation (main.tex l.1532). *)
  val gc : t -> t
end
