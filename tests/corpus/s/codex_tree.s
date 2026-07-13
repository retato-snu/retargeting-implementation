# expect: 6
def sumtree(tree) =
  match tree with
  | Leaf(v) -> return v
  | Node(left, right) ->
      let a = sumtree(left) in
      let b = sumtree(right) in
      let neg = 0 - b in
      let total = a - neg in
      return total
  end;
main =
  let l1 = Leaf(1) in
  let l2 = Leaf(2) in
  let l3 = Leaf(3) in
  let n1 = Node(l2, l3) in
  let root = Node(l1, n1) in
  let r = sumtree(root) in
  return r
