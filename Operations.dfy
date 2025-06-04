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
    requires BlackHeight(h.left) == BlackHeight(h.right)
    requires BlackHeight(h.right.left) == BlackHeight(h.right.right)
    ensures !right_leaning_red_link(result)
    ensures bst_property(result)
    ensures equal_content_property(h,result)
    ensures nodeColor(result) == nodeColor(h)
    ensures BlackHeight(result) ==BlackHeight(h)
    ensures contain(h) == contain(result)
    ensures  BlackHeight(result.left) == BlackHeight(result.right)
    ensures result.color == h.color
    ensures result.left.Node? && result.left.color == Red
    ensures isRed(result.left)
    ensures result.left.Node? ==> result.left.left == h.left
    ensures result.left.Node? ==> result.left.right == h.right.left
    ensures result.right == h.right.right
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
    requires strongLLRB(h)
    ensures strongLLRB(result)
    ensures bst_property(result)
    ensures equal_content_property(result, h)
    ensures result.Node? && result.left.Node? && result.right.Node?
    ensures  result.left.left   == h.left.left
    ensures  result.left.right  == h.left.right
    ensures  result.right.left  == h.right.left
    ensures  result.right.right == h.right.right
    ensures BlackHeight(result.left) == BlackHeight(result.right)
    ensures result.color == Red
    ensures BlackHeight(result) == BlackHeight(h)
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
    decreases contain(t)
    requires bst_property(t)
    requires strongLLRB(t)
    ensures bst_property(result)
    ensures contain(result) == contain(t) + {insert_key}
    ensures BlackHeight(t) == BlackHeight(result)
    ensures isBlack(t) ==> strongLLRB(result)
    ensures !isBlack(t) ==> weakLLRB(result) && result.color == Red
    ensures weakLLRB(result)

  {
    strongVsWeak(t);
    if t.Null? {
      result := Node(Red, insert_key, Null, Null);
      return;
    } else {
      var new_t := t;
      if isRed(t.left) && isRed(t.right) {
        assert strongLLRB(t) && isRed(t.left) && isRed(t.right);
        assert t.color == Black;
        new_t := flip_color(t);
        assert new_t.Node?;
        assert bst_property(new_t);
        assert contain(new_t) == contain(t);
        assert BlackHeight(new_t.left) == BlackHeight(new_t.right);
      }
      assert strongLLRB(t);
      assert isRed(t.left) && isRed(t.right) ==> t.color == Black && new_t.color == Red;
      assert weakLLRB(new_t);
      if insert_key > new_t.key {
        var r := insert_recur(new_t.right, insert_key);
        assert bst_property(r);
        assert bst_property(new_t.left);
        assert strongLLRB(r);
        assert strongLLRB(new_t.left);
        assert BlackHeight(new_t.left) == BlackHeight(r);
        result := Node(new_t.color, new_t.key, new_t.left, r);
        assert bst_property(result);
        // this is bst property
        assert contain(result) == contain(new_t.left) + contain(r) + {new_t.key};
        assert forall x :: x in contain(new_t.left) ==> x < new_t.key;
        assert contain(r) == {insert_key} + contain(new_t.right);
        assert forall x :: x in contain(r) ==> x > new_t.key;
        assert bst_property(result);
      } else if insert_key < new_t.key {
        var l := insert_recur(new_t.left, insert_key);
        assert strongLLRB(l.left);
        assert strongLLRB(l.right);
        result := Node(new_t.color, new_t.key, l, new_t.right);
        assert forall x :: x in contain(new_t.right) ==> x > insert_key;
        assert strongLLRB(new_t.right);
        assert BlackHeight(new_t.right) == BlackHeight(l);
      } else {
        result := new_t;
        assert weakLLRB(result);
      }
      // The new_t must has a balck right child in all case if it is a node
      assert isBlack(new_t.right);
      combination(t, result);
      assert BlackHeight(result.left) == BlackHeight(result.right);

      // What could we conclude before calling rotate left and right
      assert weakLLRB(result.left);
      assert strongLLRB(result.right);
      var before_rotate_result := result;
      if right_leaning_red_link(result) {
        var h_orig_val_debug := result; // Use a distinct name
        var X_debug := h_orig_val_debug.left;

        assert bst_property(h_orig_val_debug);
        assert BlackHeight(h_orig_val_debug.left) == BlackHeight(h_orig_val_debug.right);
        assert h_orig_val_debug.right.Node? && isRed(h_orig_val_debug.right); // From right_leaning_red_link
        assert BlackHeight(h_orig_val_debug.right.left) == BlackHeight(h_orig_val_debug.right.right);

        var result_after_rotation_debug := rotate_left(h_orig_val_debug);
        var N_new_debug := result_after_rotation_debug.left;
        result := result_after_rotation_debug;
      } else {
        assert weakLLRB(result.left);
        assert strongLLRB(result.right);
      }
      // We want to assert some prperties after possible right leaning
      black_promote(t);
      assert weakLLRB(before_rotate_result.left);
      assert weakLLRB(result.left);
      assert strongLLRB(result.right);

      if double_left_red_link(result) {
        //DLL_Contradicts_WeakLLRB_Child(result);
        result := rotate_right(result);
      }
      //assert strongLLRB(result.left);
      //assert strongLLRB(result.right);
      //assert result.color == Black ==> strongLLRB(result);
      // assert result.color == Red ==> weakLLRB(result);
      // assert isRed(result.left) && isRed(result.right) ==> result.color == Black;
      // assert !right_leaning_red_link(result);
      // //assert !double_left_red_link(result);
      // //assert goodColor(result.left);
      // assert goodColor(result.right);
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