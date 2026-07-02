(** Frame partition index φ̂ for T-sensitive abstract interpretation (main.tex ~l.992-1015). *)

type t = {
  s_label : Label.t;  (** the current S command label *)
  t_label : Label.Set.t;
}

let make ~(s_label : Label.t) ~(t_label : Label.Set.t) : t = { s_label; t_label }

let lab (p : t) : Label.t = p.s_label

let compare (a : t) (b : t) : int =
  let c = Label.compare a.s_label b.s_label in
  if c <> 0 then c else Label.Set.compare a.t_label b.t_label

let equal (a : t) (b : t) : bool = compare a b = 0

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
