(** The frame partition index [φ̂] of the retargeted, T-sensitive abstract
    interpretation of the S-coded interpreter [I_S^T] (the paper's state
    partitioning). It is the [Frame] half of the abstract part [π̂ = ⟨φ̂, κ̂⟩]; the
    continuation half [κ̂] is a stored set of caller parts and lives in
    {!S_abstract}.

    The S label alone will not do: every T expression of a given shape is
    evaluated by the {e same} syntactic occurrence of [eval], hence at the same S
    labels, so an S-label-only partitioning would join the abstract results of
    unrelated T subterms. The index therefore pairs the S label with the T view
    of the interpreter state:

    - [s_label], the current S command label — the label the frame partition
      respects (the paper's [lab]), so it is what {!lab} returns;
    - [t_label], the program labels of the T expression under evaluation, read at
      an eval-entry from field 0 of the abstract value bound to [eval]'s
      expression parameter. The value domain tracks that label {e exactly}, so
      this is a precise [Label.Set.t]; it is empty away from an eval-entry, where
      no T expression is in scope. Using a {e set} rather than a single label
      keeps the index total under joins.

    There is no top-frame component: return-site precision comes from the
    continuation index [κ̂ ∈ Kont̂ = {•}∪Lab_P] and the stored caller parts, not
    from a frame-index field. The extraction of the two components from an
    abstract state lives in {!S_abstract}. *)

(** A frame partition index. *)
type t = {
  s_label : Label.t;  (** the current S command label *)
  t_label : Label.Set.t;
      (** program labels of the T expression under evaluation; exact, possibly
          empty when no T expression is in scope at this S point *)
}

let make ~(s_label : Label.t) ~(t_label : Label.Set.t) : t = { s_label; t_label }

(** The S label an index keys (the paper's label extraction [lab]). The frame
    partitioning is label-respecting through this projection: every state in a
    partition sits at this label. *)
let lab (p : t) : Label.t = p.s_label

(** A total order, lexicographic in [s_label] then [t_label], so [t] can key a
    [Map] or [Set]. *)
let compare (a : t) (b : t) : int =
  let c = Label.compare a.s_label b.s_label in
  if c <> 0 then c else Label.Set.compare a.t_label b.t_label

let equal (a : t) (b : t) : bool = compare a b = 0

(** Render an index, e.g. [<L5 | {L1,L2}>]. *)
let to_string (p : t) : string =
  let t_labels =
    String.concat "," (List.map Label.to_string (Label.Set.elements p.t_label))
  in
  Printf.sprintf "<%s | {%s}>" (Label.to_string p.s_label) t_labels

module Map = Map.Make (struct
  type nonrec t = t

  let compare = compare
end)

module Set = Set.Make (struct
  type nonrec t = t

  let compare = compare
end)
