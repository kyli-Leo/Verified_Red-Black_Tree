include "Type.dfy"
module Property {
  import opened Type
  // predicate rb_tree_property(root: NodeC?)
  //   reads root
  // {
  //   root_property(root) &&
  //   red_property(root) &&
  //   black_property(root)


  // }

  // predicate root_property(root: NodeC?)
  //   reads root
  // {
  //   if root == null then true
  //   else !root.color
  // }

  // ghost method NodeSize(n: NodeC?) returns (s: nat)
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

  // predicate red_property(n: NodeC?)
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

  // function BlackHeight(n: NodeC?): int
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

  // predicate black_property(n: NodeC?) {
  //   BlackHeight(n) != -1
  // }


  predicate rb_tree_property_2(t: Rb_tree) {
    match t
    case Null => true
    case Node(_, _, _, _) =>
      root_property2(t) &&
      red_property2(t) &&
      black_property2(t)
  }

  // the root node should be black
  predicate root_property2(t: Rb_tree) {
    match t
    case Null => true
    case Node(color, _, _, _) => color == Black
  }

  function nodeColor(t: Rb_tree): Color
  {
    match t
    case Null => Black
    case Node(c, _, _, _) => c
  }

  // red node cannot have red childrens
  predicate red_property2(t: Rb_tree) {
    match t
    case Null => true
    case Node(color, _, left, right) =>
      if color == Red
      then nodeColor(left) == Black &&
           nodeColor(right) == Black &&
           red_property2(left) && red_property2(right)
      else red_property2(left) && red_property2(right)
  }

  function BlackHeight2(t: Rb_tree): int
  {
    match t
    case Null => 1
    case Node(color, _, left, right) =>
      var leftHeight := BlackHeight2(left);
      var rightHeight := BlackHeight2(right);
      if leftHeight != rightHeight || leftHeight == -1 || rightHeight == -1 then -1
      else if color == Black then leftHeight + 1
      else leftHeight
  }

  predicate black_property2(t: Rb_tree) {
    BlackHeight2(t) != -1
  }

  function contain(t: Rb_tree) : set<int> {
    match t
    case Null => {}
    case Node(_, key, left, right) => {key} + contain(left) + contain(right)
  }

  predicate bst_property(t:Rb_tree) {
    match t
    case Null => true
    case Node(_, key, left, right) =>
      bst_property(left) &&
      bst_property(right) &&
      (forall x :: x in contain(left) ==> x < key) &&
      (forall y :: y in contain(right) ==> y > key)
  }

  predicate equal_content_property(t1:Rb_tree, t2:Rb_tree) {
    contain(t1) == contain(t2)
  }

  function isRed(t: Rb_tree): bool {
    match t
    case Null => false
    case Node(color, _, _, _) => color == Red
  }

  function isBlack(t: Rb_tree): bool {
    match t
    case Null => true
    case Node(color, _, _, _) => color == Black
  }

  // predicate goodColor(t: Rb_tree)
  // {
  //   match t
  //   case Empty         => true
  //   case Node(c,_,l,r) =>
  //     match c
  //     case Red   => nodeColor(l) == Black && nodeColor(r) == Black
  //     case Black => nodeColor(r) == Red ==> nodeColor(l) == Red
  // }


  // predicate isLLRB (t: Rb_tree)
  // {
  //   match t
  //   case Empty         => true
  //   case Node(c,k,l,r) => isLLRB(l) && isLLRB(r) && BlackHeight2(l) == BlackHeight2(r) &&
  //                         bst_property(t) && goodColor(t)
  // }

  // predicate weakLLRB (t: Rb_tree)
  // {
  //   match t
  //   case Empty         => true
  //   case Node(c,k,l,r) => isLLRB(l) && isLLRB(r) && BlackHeight2(l) == BlackHeight2(r) &&
  //                         bst_property(t) && (nodeColor(r) == Red ==> nodeColor(l) == Red)
  // }
}