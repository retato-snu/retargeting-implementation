# count leaves of Node(Node(Leaf(9), Leaf(8)), Node(Leaf(7), Leaf(6))) = 4.
# expect: 4
def count(t) =
  match t with
  | Leaf(v) ->
      let one = 1 in
      return one
  | Node(l, r) ->
      let lc = count(l) in
      let rc = count(r) in
      let neg = 0 - rc in
      let total = lc - neg in
      return total
  end;
main =
  let nine = 9 in
  let eight = 8 in
  let seven = 7 in
  let six = 6 in
  let a = Leaf(nine) in
  let b = Leaf(eight) in
  let c = Leaf(seven) in
  let d = Leaf(six) in
  let left = Node(a, b) in
  let right = Node(c, d) in
  let root = Node(left, right) in
  let r = count(root) in
  return r
