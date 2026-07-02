(** Tree-grammar abstraction of S values (main.tex ~l.1381-1532). *)

(** {1 Abstract integers} *)
module IntSet = Domain_intf.IntSet
type aint = Domain_intf.aint = ABot | AFin of IntSet.t | AItv of int * int | ATop
let fin_safety_bound = 4096
let fin_widen_bound = 128

let aint_bot = ABot
let aint_top = ATop

(* Graded powerset/interval lattice (paper l.2000): exact [AFin] for id/label positions, escaping to [AItv] then [ATop] as numeric values grow. *)
let range : aint -> int * int = function
  | AFin s -> (IntSet.min_elt s, IntSet.max_elt s)
  | AItv (lo, hi) -> (lo, hi)
  | ABot | ATop -> invalid_arg "Domain_rtg.range"
let aint_point (n : int) : aint = AFin (IntSet.singleton n)
let aint_fin (s : IntSet.t) : aint =
  if IntSet.is_empty s then ABot
  else if IntSet.cardinal s <= fin_safety_bound then AFin s
  else AItv (IntSet.min_elt s, IntSet.max_elt s)

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
let aint_join (a : aint) (b : aint) : aint =
  match (a, b) with
  | ABot, x | x, ABot -> x
  | ATop, _ | _, ATop -> ATop
  | AFin s, AFin t -> aint_fin (IntSet.union s t)
  | _ ->
      let l1, h1 = range a and l2, h2 = range b in
      AItv (min l1 l2, max h1 h2)
let aint_mem (n : int) (a : aint) : bool =
  match a with
  | ABot -> false
  | ATop -> true
  | AFin s -> IntSet.mem n s
  | AItv (lo, hi) -> lo <= n && n <= hi
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

(** {1 Nodes, grammars, abstract values} *)
type node = { ai : aint; syms : SymSet.t }
type gram = node list Gram.t
type t = { root : node; gram : gram }

(** {1 Smart constructors and lattice on nodes / grammars} *)

(* Combiners return an operand physically when the result equals it (structural sharing). *)

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
    g1
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

(** {1 Lattice elements} *)

let bottom : t = { root = node_bot; gram = Gram.empty }

let is_bottom (v : t) : bool =
  v.root.ai = ABot && SymSet.is_empty v.root.syms

(** {1 Grammar garbage collection} *)

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
  if Gram.for_all (fun s _ -> SymSet.mem s keep) g then g
  else Gram.filter (fun s _ -> SymSet.mem s keep) g

(** [gc v] restricts [v]'s grammar to symbols reachable from the root; γ-preserving, returns [v] physically when already minimal. *)
let gc (v : t) : t =
  if Gram.is_empty v.gram then v
  else
    let keep = reachable_syms v.gram v.root.syms in
    let gram' = restrict_gram v.gram keep in
    if gram' == v.gram then v else { v with gram = gram' }

(** {1 Partial order} *)

let rec prod_leq (xs : node list) (ys : node list) : bool =
  match (xs, ys) with
  | [], [] -> true
  | x :: xs', y :: ys' -> node_leq x y && prod_leq xs' ys'
  | x :: xs', [] -> node_leq x node_bot && prod_leq xs' []
  | [], y :: ys' -> node_leq node_bot y && prod_leq [] ys'

let leq (a : t) (b : t) : bool =
  if a == b then true (* reflexivity *)
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

(** {1 Join} *)

let join (a : t) (b : t) : t =
  if a == b then a (* idempotence *)
  else if is_bottom a then b
  else if is_bottom b then a
  else { root = node_join a.root b.root; gram = gram_join a.gram b.gram }

(** {1 Widening} *)
let widen (a : t) (b : t) : t =
  if a == b then a (* [a ∇ a = a] *)
  else if is_bottom a then b
  else if is_bottom b then a
  else { root = node_widen a.root b.root; gram = gram_widen a.gram b.gram }

(** {1 Concretization and membership} *)

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

(** {1 Abstract operations required by the analysis} *)

let int_lit (n : int) : t =
  { root = { ai = aint_point n; syms = SymSet.empty }; gram = Gram.empty }

let any_int : t =
  { root = { ai = ATop; syms = SymSet.empty }; gram = Gram.empty }

let tag (site : site) (t : S_syntax.tag) (args : t list) : t =
  let arg_roots = List.map (fun a -> a.root) args in
  let merged_gram =
    List.fold_left (fun g a -> gram_join g a.gram) Gram.empty args
  in
  let sym = Sym.make site t in
  let gram =
    match Gram.find_opt sym merged_gram with
    | Some existing when List.length existing = List.length arg_roots ->
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | Some existing ->
        Gram.add sym (combine_prod node_join existing arg_roots) merged_gram
    | None -> Gram.add sym arg_roots merged_gram
  in
  (* Output is already reachable-minimal when the arguments are, so no [gc] here; GC runs at [fields] instead. *)
  { root = { ai = ABot; syms = SymSet.singleton sym }; gram }

let tag_external (t : S_syntax.tag) (args : t list) : t = tag External t args

(** Constructor-field projection [fields#_T] (main.tex ~l.1519-1531): per-site tuples of field values, each carrying the shared grammar; [None] if no such tag/arity. *)
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
  | _ ->
      let l1, h1 = range x and l2, h2 = range y in
      let cs = [ f l1 l2; f l1 h2; f h1 l2; f h1 h2 ] in
      AItv
        ( List.fold_left min (List.hd cs) (List.tl cs),
          List.fold_left max (List.hd cs) (List.tl cs) )

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
    | AItv (lo, hi) -> not (lo = 0 && hi = 0)
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
