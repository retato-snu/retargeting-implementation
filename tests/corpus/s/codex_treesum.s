# sum leaves of Node(Node(Leaf(1), Leaf(2)), Leaf(3)) = 6.
# expect: 6
def sum(t) =
  match t with
  | Leaf(v) -> return v
  | Node(l, r) ->
      let ls = sum(l) in
      let rs = sum(r) in
      let neg = 0 - rs in
      let total = ls - neg in
      return total
  end;
main =
  let one = 1 in
  let two = 2 in
  let three = 3 in
  let l1 = Leaf(one) in
  let l2 = Leaf(two) in
  let l3 = Leaf(three) in
  let left = Node(l1, l2) in
  let root = Node(left, l3) in
  let r = sum(root) in
  return r
