include "Type.dfy"
include "Property.dfy"
include "Lem.dfy"
module Operations {
  import opened Type
  import opened Property
  import opened Lem

  // This is the pre-condition for rotate_left
  predicate right_leaning_red_link(t: Rb_tree)
  {
    match t
    case Node(_, _, Null, Node(Red, _, _, _)) => true
    case Node(_, _, Node(Black, _, _, _), Node(Red, _, _, _)) => true
    case _ => false
  }

  method rotate_left(h: Rb_tree) returns (result: Rb_tree)
    requires right_leaning_red_link(h)
    requires bst_property(h)
    requires goodColor(h)
    requires BlackHeight(h.left) == BlackHeight(h.right)
    requires BlackHeight(h.right.left) == BlackHeight(h.right.right)
    ensures !right_leaning_red_link(result)
    ensures bst_property(result)
    ensures equal_content_property(h,result)
    ensures nodeColor(result) == nodeColor(h)
    ensures BlackHeight(result) ==BlackHeight(h)
    /*ensures root_property(result)
      ensures strongLLRB(result) */
    ensures contain(h) == contain(result)
    ensures result.color == h.color
    ensures result.left.Node? && result.left.color == Red
    ensures isRed(result.left)

    decreases h
  {
    var new_h := Node(Red, h.key, h.left, h.right.left);
    result := Node(h.color, h.right.key, new_h, h.right.right);
    bst_meaning(h);
    bst_transitivity_left(h);
    assert bst_property(result.left);
    assert bst_property(result.right);
    assert result.left.Node?;
    assert h.right.color == Red;
    return;
  }


  // This is the pre-condition for rotate_right
  predicate double_left_red_link(h: Rb_tree)
  {
    match h
    case Node(h_color, h_key, Node(Red, x_key, Node(Red, _, _, _), _), _) => true
    case _ => false
  }

  method rotate_right(h: Rb_tree) returns (result: Rb_tree)
    requires double_left_red_link(h)
    requires BlackHeight(h.left) == BlackHeight(h.right)
    // this is a must
    requires BlackHeight(h.left.left) == BlackHeight(h.left.right)
    requires bst_property(h)
    ensures bst_property(result)
    ensures contain(result) == contain(h)
    ensures BlackHeight(result.left) == BlackHeight(result.right)
    ensures BlackHeight(result) == BlackHeight(h)
    ensures result.color == h.color
    ensures isRed(result.left)
    ensures isRed(result.right)
    decreases h
  {
    var new_h := Node(Red, h.key, h.left.right, h.right);
    result := Node(h.color, h.left.key, h.left.left, new_h);
    assert contain(new_h) == {h.key} + contain(h.left.right) + contain(h.right);
    assert contain(result) == contain(h.left.left) + {h.left.key} + contain(new_h);
    assert new_h.key == h.key;
    assert result.key == h.left.key;

    assert forall x :: x in contain(result.left) ==> x < result.key;
    assert contain(result.right) == contain(h.left.right) + contain(h.right) + {new_h.key};
    assert forall x :: x in contain(h.left.right) ==> x > result.key;
    assert forall x :: x in contain(h.right) ==> x > new_h.key;
    assert bst_property(result.left);
    assert bst_property(h);
    bst_meaning(h);
    assert forall x :: x in contain(h.left.right) ==> x > h.left.key;
    assert forall x :: x in contain(h.right) ==> x > h.left.key;
    assert(bst_property(new_h.left));
    assert bst_property(new_h.right);
    bst_transitivity_right(h);
    assert forall x :: x in contain(new_h.left) ==> x < new_h.key;
    return;
  }


  method flip_color(h: Rb_tree) returns (result : Rb_tree)
    requires h.Node? && h.left.Node? && h.right.Node?
    requires h.left.color == Red && h.right.color == Red
    requires BlackHeight(h.left) == BlackHeight(h.right)
    requires bst_property(h)
    ensures bst_property(result)
    ensures equal_content_property(result, h)
    ensures result.Node? && result.left.Node? && result.right.Node?
    ensures  result.left.left   == h.left.left
    ensures  result.left.right  == h.left.right
    ensures  result.right.left  == h.right.left
    ensures  result.right.right == h.right.right
    ensures BlackHeight(result.left) == BlackHeight(result.right)
    decreases h
  {
    var new_left_color := (if h.left.color == Red then Black else Red);
    var new_left := Node(new_left_color, h.left.key, h.left.left, h.left.right);
    assert bst_property(h.left);
    assert bst_property(h.right);
    var new_right_color := (if h.right.color == Red then Black else Red);
    var new_right := Node(new_right_color, h.right.key, h.right.left, h.right.right);
    var result_color := ((if h.color == Red then Black else Red));
    result := Node(result_color, h.key, new_left, new_right);
    assert contain(new_left) == contain(h.left);
    assert contain(new_right) == contain(h.right);
    assert contain(result) == contain(new_left) + contain(new_right) + {h.key};
    return;
  }

  method insert_recur(t: Rb_tree, insert_key: int) returns (result :Rb_tree)
    decreases t
    requires bst_property(t)
    requires strongLLRB(t)
    ensures bst_property(result)
    ensures contain(result) == contain(t) + {insert_key}
    ensures isBlack(t) ==> strongLLRB(result)
    ensures !isBlack(t) ==> weakLLRB(result)
    ensures BlackHeight(t) == BlackHeight(result)
  {
    if t.Null? {
      result := Node(Red, insert_key, Null, Null);
    } else {
      if insert_key > t.key {
        var r := insert_recur(t.right, insert_key);
        assert bst_property(r);
        assert bst_property(t.left);
        result := Node(t.color, t.key, t.left, r);
        assert contain(result) == contain(t.left) + contain(r) + {t.key};
        assert forall x :: x in contain(t.left) ==> x < t.key;
        assert contain(r) == {insert_key} + contain(t.right);
        assert forall x :: x in contain(r) ==> x > t.key;
        assert bst_property(result);
      } else if insert_key < t.key {
        var l := insert_recur(t.left, insert_key);
        result := Node(t.color, t.key, l, t.right);
        assert forall x :: x in contain(t.right) ==> x > insert_key;
      } else {
        result := t;
      }
      //assert weakLLRB(result);
      if isRed(result.left) && isRed(result.right) {
        //result := flip_color(result);
      }

      if right_leaning_red_link(result) {
        assert result.Node?;
        assert result.right.Node? && result.right.color == Red;
        assert result.left.Null? || result.left.color == Black;
        //result := rotate_left(result);
      }

      if double_left_red_link(result) {
        ////result := rotate_right(result);
      }


    }
    return;

  }

  method makeRootBlack(t: Rb_tree) returns(result: Rb_tree)
    requires bst_property(t)
    ensures bst_property(result)
    ensures root_property(result)
    ensures root_property(result)
    ensures contain(t) == contain(result)
  {
    if t.Node? {
      result := Node(Black, t.key, t.left, t.right);
    }
    else {
      result := Null;
    }
    return;
  }

  // Wrapper function for the recursive and then change root color
  method insert(t: Rb_tree, key: int) returns (root:Rb_tree)
    requires bst_property(t)
    requires strongLLRB(t)
    requires root_property(t)
    ensures root_property(root)
    ensures bst_property(root)
    ensures contain(root) == contain(t) + {key}
  {
    root := insert_recur(t, key);
    root := makeRootBlack(root);
    return;
  }
}