(** Tree-grammar abstraction of S values (main.tex ~l.1381-1532). *)

module IntSet = Domain_intf.IntSet

type aint = Domain_intf.aint = ABot | AFin of IntSet.t | ATop

(* Cardinality past which a finite set collapses to [ATop], to keep ascending chains finite. *)
let fin_safety_bound = 4096

(* Smaller bound used only by widening, so runaway numeric chains collapse to [ATop] fast (converge quickly). *)
let fin_widen_bound = 128

let aint_bot = ABot
let aint_top = ATop

let aint_point (n : int) : aint = AFin (IntSet.singleton n)

let aint_fin (s : IntSet.t) : aint =
  if IntSet.is_empty s then ABot
  else if IntSet.cardinal s > fin_safety_bound then ATop
  else AFin s

let aint_leq (a : aint) (b : aint) : bool =
  match (a, b) with
  | ABot, _ -> true
  | _, ATop -> true
  | ATop, _ -> false
  | _, ABot -> false
  | AFin s, AFin t -> IntSet.subset s t

let aint_join (a : aint) (b : aint) : aint =
  match (a, b) with
  | ABot, x | x, ABot -> x
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t ->
      (* A stored [AFin] is within [fin_safety_bound], so a containing set is exactly the normalised union. *)
      if IntSet.subset t s then a
      else if IntSet.subset s t then b
      else aint_fin (IntSet.union s t)

let aint_mem (n : int) (a : aint) : bool =
  match a with
  | ABot -> false
  | ATop -> true
  | AFin s -> IntSet.mem n s

let aint_widen (a : aint) (b : aint) : aint =
  match (a, b) with
  | _, ABot -> a
  | ABot, x -> x
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t ->
      (* [t ⊆ s] makes the union exactly [s] (within both bounds), so the widening is [a]; share it. *)
      if IntSet.subset t s then a
      else
        let u = IntSet.union s t in
        if IntSet.cardinal u > fin_widen_bound then ATop else aint_fin u

type site = Domain_intf.site = Internal of Label.t | External

let compare_site (a : site) (b : site) : int =
  match (a, b) with
  | External, External -> 0
  | External, Internal _ -> -1
  | Internal _, External -> 1
  | Internal x, Internal y -> Label.compare x y

let string_of_site : site -> string = function
  | External -> "ext"
  | Internal l -> Label.to_string l

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

type node = { ai : aint; syms : SymSet.t }
type gram = node list Gram.t
type t = { root : node; gram : gram }

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

(* A length mismatch is defensive (same-tag productions share arity); zero-pad the shorter with [node_bot]. *)
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
  if g1 == g2 then
    (* Same object; combining a production with itself is the identity for join and widen. *)
    g1
  else
    Gram.fold
      (fun sym q acc ->
        Gram.update sym
          (function
            | None -> Some (combine_prod f [] q)
            | Some p ->
                let r = combine_prod f p q in
                (* Preserve physical sharing when the production is unchanged. *)
                if r == p then Some p else Some r)
          acc)
      g2 g1

let gram_join : gram -> gram -> gram = gram_lift node_join
let gram_widen : gram -> gram -> gram = gram_lift node_widen

let bottom : t = { root = node_bot; gram = Gram.empty }

(* A root with no symbols reaches no production, so it is the empty set regardless of its grammar. *)
let is_bottom (v : t) : bool =
  v.root.ai = ABot && SymSet.is_empty v.root.syms

(* Grammar GC: drop symbols unreachable from the root; γ-preserving (main.tex l.1532). *)
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

let restrict_gram (g : gram) (keep : SymSet.t) : gram =
  (* Returns [g] physically when nothing is dropped, keeping the grammar shared. *)
  if Gram.for_all (fun s _ -> SymSet.mem s keep) g then g
  else Gram.filter (fun s _ -> SymSet.mem s keep) g

let gc (v : t) : t =
  if Gram.is_empty v.gram then v
  else
    let keep = reachable_syms v.gram v.root.syms in
    let gram' = restrict_gram v.gram keep in
    if gram' == v.gram then v else { v with gram = gram' }

(* Node-list comparison treating absent fields as bottom. *)
let rec prod_leq (xs : node list) (ys : node list) : bool =
  match (xs, ys) with
  | [], [] -> true
  | x :: xs', y :: ys' -> node_leq x y && prod_leq xs' ys'
  | x :: xs', [] -> node_leq x node_bot && prod_leq xs' []
  | [], y :: ys' -> node_leq node_bot y && prod_leq [] ys'

(* [leq a b] iff [gamma a ⊆ gamma b]; γ is an order-embedding (main.tex ~l.1476-1482). *)
let leq (a : t) (b : t) : bool =
  if a == b then true
  else if is_bottom a then true
  else
    node_leq a.root b.root
    &&
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

(* [mem v a] decides [v ∈ gamma a] (main.tex ~l.1405-1425). *)
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

(* Finite under-approximation of [gamma]: member values of construction depth <= [depth]. *)
let sample ?(depth = 3) (a : t) : S_cek.value list =
  let int_witnesses (ai : aint) : S_cek.value list =
    match ai with
    | ABot -> []
    | AFin s -> IntSet.fold (fun n acc -> S_cek.VInt n :: acc) s []
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

(* int# (main.tex ~l.1485-1492). *)
let int_lit (n : int) : t =
  { root = { ai = aint_point n; syms = SymSet.empty }; gram = Gram.empty }

let any_int : t =
  { root = { ai = ATop; syms = SymSet.empty }; gram = Gram.empty }

(* tag#_T (main.tex ~l.1494-1517). *)
let tag (site : site) (t : S_syntax.tag) (args : t list) : t =
  let arg_roots = List.map (fun a -> a.root) args in
  let merged_gram =
    List.fold_left (fun g a -> gram_join g a.gram) Gram.empty args
  in
  let sym = Sym.make site t in
  let gram =
    match Gram.find_opt sym merged_gram with
    | Some existing when List.length existing = List.length arg_roots ->
        (* Same-site recursive value flowed back in: field-wise join with its production (paper [⊔]). *)
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | Some existing ->
        (* Defensive arity mismatch (cannot occur for a real site): [combine_prod] zero-pads, subsuming both. *)
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | None -> Gram.add sym arg_roots merged_gram
  in
  { root = { ai = ABot; syms = SymSet.singleton sym }; gram }

let tag_external (t : S_syntax.tag) (args : t list) : t = tag External t args

(* fields#_T (main.tex ~l.1519-1531): per-site tuples, no cross-site join; pure projection (GC at consumers). *)
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

let has_tag (t : S_syntax.tag) (a : t) : bool =
  SymSet.exists (fun s -> String.equal (Sym.tag s) t) a.root.syms

let has_int (a : t) : bool = a.root.ai <> ABot

let root_int (a : t) : aint = a.root.ai

let aint_binop (f : int -> int -> int) (x : aint) (y : aint) : aint =
  match (x, y) with
  | ABot, _ | _, ABot -> ABot
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t ->
      let out =
        IntSet.fold
          (fun a acc -> IntSet.fold (fun b acc -> IntSet.add (f a b) acc) t acc)
          s IntSet.empty
      in
      aint_fin out

let aint_to_val (ai : aint) : t =
  { root = { ai; syms = SymSet.empty }; gram = Gram.empty }

let sub (a : t) (b : t) : t =
  aint_to_val (aint_binop ( - ) (root_int a) (root_int b))

let mul (a : t) (b : t) : t =
  aint_to_val (aint_binop ( * ) (root_int a) (root_int b))

let abs_true : t = tag_external "True" []
let abs_false : t = tag_external "False" []

let iszero (a : t) : t =
  let ai = root_int a in
  let may_zero = aint_mem 0 ai in
  let may_nonzero =
    match ai with
    | ABot -> false
    | ATop -> true
    | AFin s -> IntSet.exists (fun n -> n <> 0) s
  in
  let parts =
    (if may_zero then [ abs_true ] else [])
    @ if may_nonzero then [ abs_false ] else []
  in
  match parts with
  | [] -> bottom
  | x :: rest -> List.fold_left join x rest

let prim (o : S_syntax.prim) (args : t list) : t option =
  match (o, args) with
  | "sub", [ a; b ] -> Some (sub a b)
  | "mul", [ a; b ] -> Some (mul a b)
  | "iszero", [ a ] -> Some (iszero a)
  | _ -> None

let string_of_aint (a : aint) : string =
  match a with
  | ABot -> "_|_"
  | ATop -> "Z"
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
