(** Generic partitioned abstract interpreter for the S core language (main.tex ~l.990-1379). *)
module Make (D : Domain_intf.DOMAIN) = struct
module Env = Map.Make (String)

(* bottom-strict: a bound variable is never bound to bottom (see aenv_add) *)
type aenv = D.t Env.t

let aenv_empty : aenv = Env.empty

let aenv_find (rho : aenv) (x : S_syntax.var) : D.t =
  match Env.find_opt x rho with Some v -> v | None -> D.bottom

(* bottom-strict: binding to bottom removes the var, since unbound reads as bottom (main.tex ~l.1086) *)
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

let aenv_leq (a : aenv) (b : aenv) : bool =
  Env.for_all
    (fun x v ->
      let bv = aenv_find b x in
      (* [v == bv] is a sound fast path: physically-equal values satisfy [v ⊑ v] *)
      v == bv || D.leq v bv)
    a

(* [κ̂ : Kont ::= {• | π̂}], [π̂ : Part ::= ⟨φ̂, κ̂⟩] (main.tex ~l.1075-1082) *)
type kelem = KEmpty | KPart of part

and part = { pphi : Partition.t; pkont : kont }

and kont = kelem list

let rec compare_kelem (a : kelem) (b : kelem) : int =
  match (a, b) with
  | KEmpty, KEmpty -> 0
  | KEmpty, KPart _ -> -1
  | KPart _, KEmpty -> 1
  | KPart p, KPart q -> compare_part p q

and compare_part (p : part) (q : part) : int =
  let c = Partition.compare p.pphi q.pphi in
  if c <> 0 then c else compare_kont p.pkont q.pkont

and compare_kont (a : kont) (b : kont) : int =
  List.compare compare_kelem a b

let kont_halt : kont = [ KEmpty ]

let rec kont_insert (e : kelem) (k : kont) : kont =
  match k with
  | [] -> [ e ]
  | x :: rest ->
      let c = compare_kelem e x in
      if c < 0 then e :: k else if c = 0 then k else x :: kont_insert e rest

let kont_union (a : kont) (b : kont) : kont = List.fold_left (fun acc e -> kont_insert e acc) b a

let kont_inter (a : kont) (b : kont) : kont =
  List.filter (fun e -> List.exists (fun e' -> compare_kelem e e' = 0) b) a

let kont_is_empty (k : kont) : bool = k = []

let string_of_kelem_short (e : kelem) : string =
  match e with
  | KEmpty -> "*"
  | KPart p -> "k" ^ Partition.to_string p.pphi

let string_of_kont (k : kont) : string =
  "{" ^ String.concat "," (List.map string_of_kelem_short k) ^ "}"

(* finite-push: truncates the inner continuation to [{•}], bounding reachable parts (main.tex ~l.1029-1041) *)
let pushk (phi : Partition.t) (_k : kont) : kont =
  [ KPart { pphi = phi; pkont = kont_halt } ]

(* [pusĥ⁻¹(κ̂')]: the write-back filter [κ̂' ∩ pusĥ⁻¹(κ̂')] (main.tex ~l.1323) *)
let push_inv (k : kont) : kont =
  List.filter
    (fun e ->
      match e with
      | KEmpty -> true
      | KPart p -> compare_kont p.pkont kont_halt = 0)
    k

module Key = struct
  type t = Partition.t * kont

  let compare ((p1, k1) : t) ((p2, k2) : t) : int =
    let c = Partition.compare p1 p2 in
    if c <> 0 then c else compare_kont k1 k2
end

module Table = Map.Make (Key)

type entry = { rho : aenv; kont : kont }
type state = entry Table.t

let state_empty : state = Table.empty

let table_find (sigma : state) (key : Key.t) : entry =
  match Table.find_opt key sigma with
  | Some e -> e
  | None -> { rho = aenv_empty; kont = [] }

let part_of_key ((phi, k) : Key.t) : part = { pphi = phi; pkont = k }

module KeySet = Set.Make (Key)

let kont_mentioned_phis (k : kont) : Partition.t list =
  List.filter_map
    (fun (e : kelem) -> match e with KEmpty -> None | KPart p -> Some p.pphi)
    k

type index = {
  mutable fwd : kont list Partition.Map.t;
  mutable rev : KeySet.t Partition.Map.t;
  is_return : Partition.t -> bool;
}

let pmap_find_list (m : kont list Partition.Map.t) (phi : Partition.t) : kont list
    =
  match Partition.Map.find_opt phi m with Some l -> l | None -> []

let pmap_find_set (m : KeySet.t Partition.Map.t) (phi : Partition.t) : KeySet.t =
  match Partition.Map.find_opt phi m with Some s -> s | None -> KeySet.empty

let idx_record (idx : index) ((phi, k) : Key.t) ~(old_kont : kont)
    ~(new_kont : kont) ~(is_new_key : bool) : unit =
  if is_new_key then
    idx.fwd <- Partition.Map.add phi (k :: pmap_find_list idx.fwd phi) idx.fwd;
  if idx.is_return phi then begin
    let old_mentions = kont_mentioned_phis old_kont in
    let newly =
      List.filter
        (fun p -> not (List.exists (fun q -> Partition.equal p q) old_mentions))
        (kont_mentioned_phis new_kont)
    in
    List.iter
      (fun pc ->
        idx.rev <-
          Partition.Map.add pc
            (KeySet.add (phi, k) (pmap_find_set idx.rev pc))
            idx.rev)
      newly
  end

let index_of_state (is_return : Partition.t -> bool) (sigma : state) : index =
  let idx = { fwd = Partition.Map.empty; rev = Partition.Map.empty; is_return } in
  Table.iter
    (fun key (e : entry) ->
      idx_record idx key ~old_kont:[] ~new_kont:e.kont ~is_new_key:true)
    sigma;
  idx

type handle = {
  prog : S_syntax.program;
  eval_entry : Label.t;
  eval_e : S_syntax.var;
  eval_call_labels : Label.Set.t;
  in_scope : S_syntax.var list Label.Map.t;
}

(* support of the [env : Frame → Env] map (main.tex ~l.1017-1027) *)
let compute_in_scope (prog : S_syntax.program)
    (seed_vars : (Label.t * S_syntax.var list) list) :
    S_syntax.var list Label.Map.t =
  let module SS = Set.Make (String) in
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
        []
    | S_syntax.LetTag (x, _, _, k) -> [ (k, SS.add x bound) ]
    | S_syntax.Match (_, branches) ->
        List.map
          (fun (S_syntax.PTag (_, vars), k) ->
            (k, List.fold_left (fun s v -> SS.add v s) bound vars))
          branches
  in
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

let env_of_frame (h : handle) (phi : Partition.t) : string list =
  in_scope_at h (Partition.lab phi)

(* the indexed write-back's [ρ̂' ⊓ env(φ̂')] (main.tex ~l.1322) *)
let aenv_meet_scope (rho : aenv) (scope : string list) : aenv =
  let module SS = Set.Make (String) in
  let keep = SS.of_list scope in
  Env.filter (fun x _ -> SS.mem x keep) rho

let handle_for_interp () : handle =
  let pts = Projection.points in
  let eval_call_labels =
    List.fold_left
      (fun acc (l, _) -> Label.Set.add l acc)
      Label.Set.empty
      pts.Projection.Points.call_frames
  in
  {
    prog = Interp_st.program;
    eval_entry = pts.Projection.Points.eval_entry;
    eval_e = pts.Projection.Points.eval_e;
    eval_call_labels;
    in_scope =
      compute_in_scope Interp_st.program
        [ (Interp_st.program.S_syntax.main, [ Interp_st.arg_p; Interp_st.arg_arg ]) ];
  }

(* abstract expression evaluation [eval#] (main.tex ~l.1152-1184) *)
let abs_atom (rho : aenv) (a : S_syntax.atom) : D.t =
  match a with
  | S_syntax.AInt n -> D.int_lit n
  | S_syntax.AVar x -> aenv_find rho x

(* [None] flags an uninterpreted (stuck) primitive: contributes no successor (sound) *)
let abs_rhs (rho : aenv) (r : S_syntax.rhs) : D.t option =
  match r with
  | S_syntax.Atom a -> Some (abs_atom rho a)
  | S_syntax.Prim (o, args) -> D.prim o (List.map (abs_atom rho) args)

let t_labels_of_value (v : D.t) : Label.Set.t =
  let expr_tags =
    [
      (T_encoding.tag_int, 2);
      (T_encoding.tag_var, 2);
      (T_encoding.tag_sub, 3);
      (T_encoding.tag_mul, 3);
      (T_encoding.tag_let, 4);
      (T_encoding.tag_app, 3);
      (T_encoding.tag_ifz, 4);
    ]
  in
  let add_exact (acc : Label.Set.t) (field0 : D.t) : Label.Set.t =
    match D.root_int field0 with
    | D.AFin s ->
        Domain_intf.IntSet.fold (fun n acc -> Label.Set.add n acc) s acc
    | D.ABot | D.ATop -> acc
  in
  List.fold_left
    (fun acc (tag, arity) ->
      if D.has_tag tag v then
        match D.fields tag arity v with
        | Some tuples ->
            List.fold_left
              (fun acc tuple ->
                match tuple with field0 :: _ -> add_exact acc field0 | [] -> acc)
              acc tuples
        | None -> acc
      else acc)
    Label.Set.empty expr_tags

let partition_of (h : handle) (l : Label.t) (rho : aenv) : Partition.t =
  let t_label =
    if Label.equal l h.eval_entry then t_labels_of_value (aenv_find rho h.eval_e)
    else Label.Set.empty
  in
  Partition.make ~s_label:l ~t_label

(* view-indexed abstract step: [AbsLetExp]/[AbsLetCall]/[AbsReturn]/[AbsMatch] (main.tex ~l.1198-1278) *)
type succ = Key.t * aenv * kont

let find_fun (h : handle) (f : S_syntax.var) : S_syntax.fundef option =
  List.find_opt
    (fun (d : S_syntax.fundef) -> String.equal d.S_syntax.name f)
    h.prog.S_syntax.funs

let step_entry ?(idx : index option) (h : handle) (sigma : state)
    ((phi, k) : Key.t) (rho : aenv) (kont : kont) : succ list =
  let l = Partition.lab phi in
  match S_syntax.cmd_at h.prog l with
  | S_syntax.Return a ->
      (* AbsReturn (main.tex ~l.1231-1257), realized under the finite push: resume into every entry stored at φ̂_c *)
      let v = abs_atom rho a in
      let resume_at phi_c x cont =
        match idx with
        | Some idx ->
            List.filter_map
              (fun ck ->
                match Table.find_opt (phi_c, ck) sigma with
                | None -> None
                | Some centry ->
                    let rho_c = aenv_add x v centry.rho in
                    let phi' = partition_of h cont rho_c in
                    Some (((phi', ck), rho_c, ck) : succ))
              (pmap_find_list idx.fwd phi_c)
        | None ->
            Table.fold
              (fun ((cphi, ck) : Key.t) (centry : entry) acc ->
                if Partition.equal cphi phi_c then
                  let rho_c = aenv_add x v centry.rho in
                  let phi' = partition_of h cont rho_c in
                  (((phi', ck), rho_c, ck) : succ) :: acc
                else acc)
              sigma []
      in
      List.concat_map
        (fun (e : kelem) ->
          match e with
          | KEmpty -> []
          | KPart caller -> (
              let phi_c = caller.pphi in
              match S_syntax.cmd_at h.prog (Partition.lab phi_c) with
              | S_syntax.LetCall (x, _f, _args, cont) -> resume_at phi_c x cont
              | _ -> []))
        kont
  | S_syntax.Let (x, r, cont) -> (
      (* AbsLetExp (main.tex ~l.1198-1214) *)
      match abs_rhs rho r with
      | None -> []
      | Some v ->
          let rho' = aenv_add x v rho in
          let phi' = partition_of h cont rho' in
          [ ((phi', k), rho', kont) ])
  | S_syntax.LetCall (_x, f, args, _cont) -> (
      (* AbsLetCall (main.tex ~l.1216-1229), posting the finite [pusĥ(φ̂, κ̂)] *)
      match find_fun h f with
      | None -> []
      | Some def ->
          let arg_vals = List.map (abs_atom rho) args in
          if List.length def.S_syntax.params <> List.length arg_vals then []
          else
            let callee_rho =
              List.fold_left2
                (fun e param v -> aenv_add param v e)
                aenv_empty def.S_syntax.params arg_vals
            in
            let callee_kont = pushk phi kont in
            let phi' = partition_of h def.S_syntax.entry callee_rho in
            [ ((phi', callee_kont), callee_rho, callee_kont) ])
  | S_syntax.LetTag (x, t, args, cont) ->
      (* AbsLetTag: allocate a tagged value at this command's label as the allocation site *)
      let arg_vals = List.map (abs_atom rho) args in
      let v = D.tag (D.Internal l) t arg_vals in
      let rho' = aenv_add x v rho in
      let phi' = partition_of h cont rho' in
      [ ((phi', k), rho', kont) ]
  | S_syntax.Match (a, branches) ->
      (* AbsMatch (main.tex ~l.1259-1278): one successor per tuple in [fields#_T(tag, arity, scrut)] *)
      let scrut = abs_atom rho a in
      List.concat_map
        (fun (S_syntax.PTag (tag, vars), cont) ->
          let arity = List.length vars in
          if D.has_tag tag scrut then
            match D.fields tag arity scrut with
            | Some tuples ->
                List.filter_map
                  (fun tuple ->
                    if List.length tuple = arity then
                      (* GC the projected field grammar before storing (main.tex l.1532) *)
                      let rho' =
                        List.fold_left2
                          (fun e y v -> aenv_add y (D.gc v) e)
                          rho vars tuple
                      in
                      let phi' = partition_of h cont rho' in
                      Some ((phi', k), rho', kont)
                    else None)
                  tuples
            | None -> []
          else [])
        branches

(* worklist fixpoint of the full transfer function (main.tex ~l.1329-1374) *)

(* indexed write-back refinement [⊓ env(φ̂')], [∩ pusĥ⁻¹(κ̂')] (main.tex AbsStep ~l.1287-1327) *)
let refine_succ (h : handle) (((phi', k'), rho', kont') : succ) : succ =
  let rho_ref = aenv_meet_scope rho' (env_of_frame h phi') in
  let kont_ref = kont_inter kont' (push_inv k') in
  ((phi', k'), rho_ref, kont_ref)

(* reverse edge: re-process every Return entry whose continuation names a grown caller frame [φ̂_c] *)
let is_caller_key (h : handle) ((phi, _) : Key.t) : bool =
  match S_syntax.cmd_at h.prog (Partition.lab phi) with
  | S_syntax.LetCall _ -> true
  | _ -> false

let kont_mentions_phi (k : kont) (phi : Partition.t) : bool =
  List.exists
    (fun (e : kelem) ->
      match e with KEmpty -> false | KPart p -> Partition.equal p.pphi phi)
    k

let dependents ?(idx : index option) (h : handle) (sigma : state) (key : Key.t) :
    Key.t list =
  let phi_c, _ = key in
  if is_caller_key h key then
    match idx with
    | Some idx ->
        KeySet.fold (fun k acc -> k :: acc) (pmap_find_set idx.rev phi_c) [ key ]
    | None ->
        Table.fold
          (fun ((rphi, _) as rkey) (rentry : entry) acc ->
            if kont_mentions_phi rentry.kont phi_c then
              match S_syntax.cmd_at h.prog (Partition.lab rphi) with
              | S_syntax.Return _ -> rkey :: acc
              | _ -> acc
            else acc)
          sigma [ key ]
  else [ key ]

let update ?(idx : index option) (sigma : state) (((key, rho, kont) : succ)) :
    state * bool =
  if Env.is_empty rho && kont_is_empty kont then (sigma, false)
  else
    match Table.find_opt key sigma with
    | None ->
        (match idx with
        | Some idx -> idx_record idx key ~old_kont:[] ~new_kont:kont ~is_new_key:true
        | None -> ());
        (Table.add key { rho; kont } sigma, true)
    | Some old ->
        (* growth-detection fast path: [¬(rho ⊑ old.rho)] is equivalent to the unfused widen but avoids materializing it *)
        let grew_rho = not (aenv_leq rho old.rho) in
        let new_kont = kont_union old.kont kont in
        let grew_kont = compare_kont new_kont old.kont <> 0 in
        if (not grew_rho) && not grew_kont then (sigma, false)
        else begin
          let widened_rho = aenv_widen old.rho (aenv_join old.rho rho) in
          (match idx with
          | Some idx when grew_kont ->
              idx_record idx key ~old_kont:old.kont ~new_kont ~is_new_key:false
          | _ -> ());
          (Table.add key { rho = widened_rho; kont = new_kont } sigma, true)
        end

(* [max_steps] is a defensive guard, never the binding limit (finiteness + widening terminate) *)
let solve ?(max_steps = 5_000_000) (h : handle) (init : state) : state =
  let module KeySet = Set.Make (Key) in
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
      | None -> sigma
      | Some key ->
          let worklist = KeySet.remove key worklist in
          let e = table_find sigma key in
          let succs = step_entry ~idx h sigma key e.rho e.kont in
          let sigma', changed_keys =
            List.fold_left
              (fun (sg, chg) raw ->
                let succ = refine_succ h raw in
                let sg', changed = update ~idx sg succ in
                let key', _, _ = succ in
                if changed then
                  ( sg',
                    List.fold_left
                      (fun acc k -> KeySet.add k acc)
                      chg
                      (dependents ~idx h sg' key') )
                else (sg', chg))
              (sigma, KeySet.empty) succs
          in
          loop (steps - 1) sigma' (KeySet.union worklist changed_keys)
  in
  loop max_steps init initial_keys

type analysis = { table : state; result : D.t }

let initial_env (encoded_p : D.t) (arg : D.t) : aenv =
  aenv_add Interp_st.arg_p encoded_p (aenv_add Interp_st.arg_arg arg aenv_empty)

(* kept well above interpreter command labels so input-node sites never collide with interpreter [LetTag] sites *)
let input_site_base = 1_000_000

let abstract_value (v : S_cek.value) : D.t =
  let next = ref input_site_base in
  let fresh_site () =
    let l = !next in
    incr next;
    D.Internal l
  in
  let rec go (v : S_cek.value) : D.t =
    match v with
    | S_cek.VInt n -> D.int_lit n
    | S_cek.VTag (t, vs) -> D.tag (fresh_site ()) t (List.map go vs)
  in
  go v

let read_result (h : handle) (sigma : state) : D.t =
  Table.fold
    (fun (phi, _) (e : entry) acc ->
      if List.exists (fun el -> compare_kelem el KEmpty = 0) e.kont then
        match S_syntax.cmd_at h.prog (Partition.lab phi) with
        | S_syntax.Return a -> D.join acc (abs_atom e.rho a)
        | _ -> acc
      else acc)
    sigma D.bottom

let analyze ?(arg : D.t = D.int_lit 0) (encoded_p : S_cek.value)
    : analysis =
  let h = handle_for_interp () in
  let rho0 = initial_env (abstract_value encoded_p) arg in
  let phi0 = partition_of h h.prog.S_syntax.main rho0 in
  let init =
    Table.add (phi0, kont_halt) { rho = rho0; kont = kont_halt } state_empty
  in
  let table = solve h init in
  { table; result = read_result h table }

let analyze_t ?(arg : D.t = D.int_lit 0)
    (p : T_encoding.program) : analysis =
  analyze ~arg (T_encoding.enc_program p)

let table_size (sigma : state) : int = Table.cardinal sigma

let partitions (sigma : state) : Partition.Set.t =
  Table.fold (fun (phi, _) _ acc -> Partition.Set.add phi acc) sigma
    Partition.Set.empty

let has_partition_with_t_label (sigma : state) ~(s_label : Label.t)
    ~(t_label : Label.t) : bool =
  Table.exists
    (fun (phi, _) _ ->
      Label.equal (Partition.lab phi) s_label
      && Label.Set.mem t_label phi.Partition.t_label)
    sigma

end

(* default instantiation: the concrete RTG value domain *)
include Make (Domain_rtg)
