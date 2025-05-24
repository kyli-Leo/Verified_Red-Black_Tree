include "Type.dfy"
module Property {
  import opened Type
  // predicate rb_tree_property(root: Node?)
  //   reads root
  // {
  //   root_property(root) &&
  //   red_property(root) &&
  //   black_property(root)


  // }

  // predicate root_property(root: Node?)
  //   reads root
  // {
  //   if root == null then true
  //   else !root.color
  // }

  // ghost method NodeSize(n: Node?) returns (s: nat)
  //   decreases n
  // {
  //   if n == null {
  //     s := 0;
  //   } else {
  //     var l := 0;
  //     var r := 0;
  //     l := NodeSize(n.left);
  //     r := NodeSize(n.right);
  //     s := 1 + l + r;
  //   }
  // }

  // predicate red_property(n: Node?)
  //   reads *
  //   decreases n
  // {
  //   if n == null then true
  //   else if n.color then
  //     (n.left == null || !n.left.color) &&
  //     (n.right == null || !n.right.color) &&
  //     red_property(n.left) &&
  //     red_property(n.right)
  //   else
  //     red_property(n.left) &&
  //     red_property(n.right)
  // }

  // function BlackHeight(n: Node?): int
  //   decreases n
  // {
  //   // this implies leaf property
  //   if n == null then 1
  //   else
  //     var left_height := BlackHeight(n.left);
  //     var right_height := BlackHeight(n.right);
  //     // We use -1 to show that it is invalid
  //     if left_height == -1 || right_height == -1 || left_height != right_height then -1
  //     else left_height + (if n.color then 0 else 1)
  // }

  // predicate black_property(n: Node?) {
  //   BlackHeight(n) != -1
  // }


  predicate rb_tree_property_2(t: Rb_tree) {
    match t
    case Null => true
    case Node(_, _, _, _) => root_property2(t)
  }

  predicate root_property2(t: Rb_tree) {
    match t
    case Null => true
    case Node(color, _, _, _) => color == Black
  }
  // Helper predicate
  function isBlack(t: Rb_tree) : bool {
    match t
    case Null => true
    case Node(c, _, _, _) => c == Black
  }

  predicate red_property2(t: Rb_tree) {
    match t
    case Null => true
    case Node(color, _, left, right) =>
      if color == Red then isBlack(left) && isBlack(right) && red_property2(left) && red_property2(right)
      else red_property2(left) && red_property2(right)
  }

  function BlackHeight2(t: Rb_tree): int
  {
    match t
    case Null => 1
    case Node(color, _, left, right) =>
      var leftHeight := BlackHeight2(left);
      var rightHeight := BlackHeight2(right);
      if leftHeight != rightHeight then -1
      else if color == Black then leftHeight + 1
      else leftHeight
  }

  predicate black_property(t: Rb_tree) {
    BlackHeight2(t) != -1
  }

}