# Depth of a binary tree: depth(Leaf) = 1, depth(Node(l,r)) = 1 + max(depth l,
# depth r). max(a,b) is selected by a recursive leq built from iszero/sub
# (leq(a,b) walks both down by 1 until one hits zero). +1 is written 1 - (0 - d).
# Tree Node(Node(Node(Leaf, Leaf), Leaf), Leaf) is left-leaning of depth 4:
#   depth(Leaf)=1; depth(Node(Leaf,Leaf))=2; depth(Node(that,Leaf))=3; root=4.
# expect: 4
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
def max2(a, b) =
  let ok = leq(a, b) in
  match ok with
  | True() -> return b
  | False() -> return a
  end;
def depth(t) =
  match t with
  | Leaf() -> return 1
  | Node(l, r) ->
      let dl = depth(l) in
      let dr = depth(r) in
      let m = max2(dl, dr) in
      let neg = 0 - 1 in
      let d = m - neg in
      return d
  end;
main =
  let lf = Leaf() in
  let lf2 = Leaf() in
  let lf3 = Leaf() in
  let lf4 = Leaf() in
  let n1 = Node(lf, lf2) in
  let n2 = Node(n1, lf3) in
  let root = Node(n2, lf4) in
  let r = depth(root) in
  return r
