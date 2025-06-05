include "Type.dfy"
module Property {
  import opened Type
  predicate rootProperty(t: Rb_tree) {
    match t
    case Null => true
    case Node(nodeColor, _, _, _) => nodeColor == Black
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
    case Node(nodeColor, _, left, right) =>
      var leftHeight := BlackHeight(left);
      var rightHeight := BlackHeight(right);
      var result := Max(leftHeight, rightHeight);
      if nodeColor == Black then result + 1
      else result
  }

  function contain(t: Rb_tree) : set<int> {
    match t
    case Null => {}
    case Node(_, key, left, right) => {key} + contain(left) + contain(right)
  }

  predicate bstProperty(t:Rb_tree) {
    match t
    case Null => true
    case Node(_, key, left, right) =>
      bstProperty(left) &&
      bstProperty(right) &&
      (forall x :: x in contain(left) ==> x < key) &&
      (forall y :: y in contain(right) ==> y > key)
  }

  predicate equalContentProperty(t1:Rb_tree, t2:Rb_tree) {
    contain(t1) == contain(t2)
  }

  function isRed(t: Rb_tree): bool {
    match t
    case Null => false
    case Node(nodeColor, _, _, _) => nodeColor == Red
  }

  function isBlack(t: Rb_tree): bool {
    match t
    case Null => true
    case Node(nodeColor, _, _, _) => nodeColor == Black
  }

  // This is the pre-condition for rotate_right
  predicate doubleLeftRedLink(h: Rb_tree)
  {
    match h
    case Node(h_nodeColor, h_key, Node(Red, x_key, Node(Red, _, _, _), _), _) => true
    case _ => false
  }

  predicate goodColor(t: Rb_tree)
  {
    match t
    case Null => true
    case Node(c,_,l,r) =>
      if c == Red then nodeColor(l) == Black && nodeColor(r) == Black
      else nodeColor(r) == Red ==> nodeColor(l) == Red
  }


  predicate strongLLRB (t: Rb_tree)
  {
    match t
    case Null => true
    case Node(c,k,l,r) => strongLLRB(l) && strongLLRB(r) && BlackHeight(l) == BlackHeight(r) &&
                          bstProperty(t) && goodColor(t)
  }

  predicate weakLLRB (t: Rb_tree)
  {
    match t
    case Null => true
    case Node(c,k,l,r) => strongLLRB(l) && strongLLRB(r) && BlackHeight(l) == BlackHeight(r) &&
                          bstProperty(t) && (nodeColor(r) == Red ==> nodeColor(l) == Red)
  }

}