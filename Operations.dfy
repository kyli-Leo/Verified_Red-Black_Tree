include "Type.dfy"
include "Property.dfy"
module Operations {
  import opened Type
  import opened Property

  // This is the pre-condition for rotate_left
  predicate right_leaning_red_link(t: Rb_tree)
  {
    match t
    case Node(_, _, Null, Node(Red, _, _, _)) => true
    case Node(_, _, Node(Black, _, _, _), Node(Red, _, _, _)) => true
    case _ => false
  }

  function rotate_left(h: Rb_tree): Rb_tree
    requires right_leaning_red_link(h)
    ensures !right_leaning_red_link(rotate_left(h))
    decreases h
  {
    match h
    case Node(h_color, h_key, h_left, h_right) =>
      match h_right
      case Node(Red, x_key, x_left, x_right) =>
        var new_h := Node(Red, h_key, h_left, x_left);
        var new_x := Node(h_color, x_key, new_h, x_right);
        new_x
  }


  // This is the pre-condition for rotate_right
  predicate double_left_red_link(h: Rb_tree)
  {
    match h
    case Node(h_color, h_key, Node(Red, x_key, Node(Red, _, _, _), _), _) => true
    case _ => false
  }

  function rotate_right(h: Rb_tree): Rb_tree
    requires h.Node?
    requires double_left_red_link(h)
    // requires !right_leaning_red_link(h) true but the proof uhhhh
    requires h.color == Black
    ensures !double_left_red_link(rotate_right(h))
    decreases h
  {
    match h
    case Node(h_color, h_key, Node(Red, x_key, Node(Red, ll_key, ll_left, ll_right), x_right), h_right) =>
      var new_h := Node(Red, h_key, x_right, h_right);
      var new_x := Node(h_color, x_key, Node(Red, ll_key, ll_left, ll_right), new_h);
      assert new_x.color == h_color;
      new_x
  }


  // this is the precondition for color flip
  predicate hasRedChildren(h: Rb_tree)
  {
    match h
    // I think we might need to help dafny to prove that this node is black
    case Node(Black, _, Node(Red, _, _, _), Node(Red, _, _, _)) => true
    case _ => false
  }

  function flip_color(h: Rb_tree): Rb_tree
    requires hasRedChildren(h)
    ensures !hasRedChildren(flip_color(h))
    decreases h
  {
    match h
    case Node(_, key, Node(_, l_key, l_left, l_right), Node(_, r_key, r_left, r_right)) =>
      var new_left := Node(Black, l_key, l_left, l_right);
      var new_right := Node(Black, r_key, r_left, r_right);
      var new_h := Node(Red, key, new_left, new_right);
      new_h
  }

  function nodeColor(t: Rb_tree): Color
  {
    match t
    case Null => Black
    case Node(c, _, _, _) => c
  }

  function insert_recur(t: Rb_tree, key: int): Rb_tree
    decreases t
  {
    var inserted := match t
      case Null => Node(Red, key, Null, Null)
      case Node(color, k, left, right) =>
        if key < k then Node(color, k, insert_recur(left, key), right)
        else if key > k then Node(color, k, left, insert_recur(right, key))
        else Node(color, k, left, right);

    var step1 := if nodeColor(inserted.right) == Red && nodeColor(inserted.left) == Black
                 then rotate_left(inserted)
                 else inserted;

    var step2 := match step1
      case Node(_, _, Node(Red, _, Node(Red, _, _, _), _), _) => rotate_right(step1)
      case _ => step1;

    var step3 := match step2
      case Node(Black, _, Node(Red, _, _, _), Node(Red, _, _, _)) => flip_color(step2)
      case _ => step2;

    step3
  }
  // Wrapper function for the recursive and then change root color
  function insert(t: Rb_tree, key: int): Rb_tree
    requires rb_tree_property_2(t)
    ensures rb_tree_property_2(insert(t, key))
  {
    var new_tree := insert_recur(t, key);

    //Ensure the root is always Black from the side effect of flipcolor
    match new_tree
    case Null => Null
    case Node(_, k, l, r) => Node(Black, k, l, r)
  }
}