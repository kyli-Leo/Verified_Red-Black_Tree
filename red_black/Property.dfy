include "Type.dfy"
module Property {
  import opened Type

  function GetColor(t: RbTree): Color {
    match t
    case Null => Black // NIL leaves are considered Black
    case Node(c, _, _, _) => c
  }

  function IsRed(t: RbTree): bool {
    GetColor(t) == Red
  }

  function IsBlack(t: RbTree): bool {
    GetColor(t) == Black
  }

  // BST Property (same as your LLRB version)
  function contain(t: RbTree) : set<int> {
    match t
    case Null => {}
    case Node(_, k, l, r) => {k} + contain(l) + contain(r)
  }

  predicate bst_property(k: int, l: RbTree, r: RbTree) {
    (forall x :: x in contain(l) ==> x < k) &&
    (forall y :: y in contain(r) ==> y > k)
  }

  predicate is_bst(t: RbTree) {
    match t
    case Null => true
    case Node(_, k, l, r) =>
      bst_property(k, l, r) &&
      is_bst(l) &&
      is_bst(r)
  }

  // Red-Red Violation (Invariant 4: If a node is Red, its children are Black)
  predicate noRedRedViolation(t: RbTree) {
    match t
    case Null => true
    case Node(c, k , l, r) =>
      (if c == Red then IsBlack(l) && IsBlack(r) else true) &&
      noRedRedViolation(l) &&
      noRedRedViolation(r)
  }

  // Black-Height Property (Invariant 5)
  // Returns posivie number if equal black height for all path, -1 if unbalanced
  function BlackHeight(t: RbTree): int
  {
    match t
    case Null => 1
    case Node(color, _, left, right) =>
      var leftHeight := BlackHeight(left);
      var rightHeight := BlackHeight(right);
      if leftHeight != rightHeight || leftHeight == -1 || rightHeight == -1 then -1
      else if color == Black then leftHeight + 1
      else leftHeight
  }

  predicate IsRbSubTree(t: RbTree) {
    is_bst(t) &&
    noRedRedViolation(t) &&
    BlackHeight(t) >= 1
  }

  // Full RB Tree Invariant (root must be Black)
  predicate IsRbTree(t: RbTree) {
    IsRbSubTree(t) &&
    (t.Null? || IsBlack(t)) // Root is Black (or tree is Empty)
  }

  predicate equal_content_property(t1:RbTree, t2:RbTree) {
    contain(t1) == contain(t2)
  }

  function isRed(t: RbTree): bool {
    match t
    case Null => false
    case Node(color, _, _, _) => color == Red
  }

  function isBlack(t: RbTree): bool {
    match t
    case Null => true
    case Node(color, _, _, _) => color == Black
  }

  // This is the pre-condition for rotate_right
  predicate double_left_red_link(h: RbTree)
  {
    match h
    case Node(h_color, h_key, Node(Red, x_key, Node(Red, _, _, _), _), _) => true
    case _ => false
  }
}