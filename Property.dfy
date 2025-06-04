include "Type.dfy"
module Property {
  import opened Type
  predicate root_property(t: Rb_tree) {
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

  function Max(left:int , right:int):int
  {
    if left >= right then left
    else right
  }

  function BlackHeight(t: Rb_tree): int
  {
    match t
    case Null => 1
    case Node(color, _, left, right) =>
      var leftHeight := BlackHeight(left);
      var rightHeight := BlackHeight(right);
      var result := Max(leftHeight, rightHeight);
      if color == Black then result + 1
      else result
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

  // This is the pre-condition for rotate_right
  predicate double_left_red_link(h: Rb_tree)
  {
    match h
    case Node(h_color, h_key, Node(Red, x_key, Node(Red, _, _, _), _), _) => true
    case _ => false
  }

  predicate goodColor(t: Rb_tree)
  {
    match t
    case Null => true
    case Node(color,_,l,r) =>
      if color == Red then nodeColor(l) == Black && nodeColor(r) == Black
      else nodeColor(r) == Red ==> nodeColor(l) == Red
  }


  predicate strongLLRB (t: Rb_tree)
  {
    match t
    case Null => true
    case Node(c,k,l,r) => strongLLRB(l) && strongLLRB(r) && BlackHeight(l) == BlackHeight(r) &&
                          bst_property(t) && goodColor(t)
  }

  predicate weakLLRB (t: Rb_tree)
  {
    match t
    case Null => true
    case Node(c,k,l,r) => strongLLRB(l) && strongLLRB(r) && BlackHeight(l) == BlackHeight(r) &&
                          bst_property(t) && (nodeColor(r) == Red ==> nodeColor(l) == Red)
  }

}