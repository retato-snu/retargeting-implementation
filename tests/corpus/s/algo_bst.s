# Binary search tree: insert a few keys, then look one up. A node is
# Node(key, left, right); an empty subtree is Leaf(). Ordering is decided by a
# recursive leq (iszero/sub only). insert(k, t) descends left when leq(k, key),
# else right. lookup(k, t) returns True()/False(): equal (leq both ways) -> True,
# else recurse into the side leq selects. Inserting 5,3,8,1 builds
#   Node(5, Node(3, Node(1, Leaf, Leaf), Leaf), Node(8, Leaf, Leaf));
# lookup(8) finds the right child -> True().
# expect: True()
def leq(a, b) =
  let za = iszero(a) in
  match za with
  | True() -> return za
  | False() ->
      let zb = iszero(b) in
      match zb with
      | True() ->
          let f = False() in
          return f
      | False() ->
          let a1 = a - 1 in
          let b1 = b - 1 in
          let r = leq(a1, b1) in
          return r
      end
  end;
def insert(k, t) =
  match t with
  | Leaf() ->
      let e1 = Leaf() in
      let e2 = Leaf() in
      let node = Node(k, e1, e2) in
      return node
  | Node(key, l, r) ->
      let ok = leq(k, key) in
      match ok with
      | True() ->
          let l2 = insert(k, l) in
          let node = Node(key, l2, r) in
          return node
      | False() ->
          let r2 = insert(k, r) in
          let node = Node(key, l, r2) in
          return node
      end
  end;
def lookup(k, t) =
  match t with
  | Leaf() ->
      let f = False() in
      return f
  | Node(key, l, r) ->
      let le = leq(k, key) in
      let ge = leq(key, k) in
      match le with
      | True() ->
          match ge with
          | True() ->
              let tt = True() in
              return tt
          | False() ->
              let rl = lookup(k, l) in
              return rl
          end
      | False() ->
          let rr = lookup(k, r) in
          return rr
      end
  end;
main =
  let e = Leaf() in
  let t1 = insert(5, e) in
  let t2 = insert(3, t1) in
  let t3 = insert(8, t2) in
  let t4 = insert(1, t3) in
  let r = lookup(8, t4) in
  return r
