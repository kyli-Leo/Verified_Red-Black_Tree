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





}