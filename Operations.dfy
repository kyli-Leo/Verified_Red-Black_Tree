include "Type.dfy"
include "Property.dfy"
include "Lem.dfy"
module Operations {
  import opened Type
  import opened Property
  import opened Lem

  // This is the pre-condition for rotateLeft
  predicate rightLeaningRedLink(t: Rb_tree)
  {
    match t
    case Node(_, _, Null, Node(Red, _, _, _)) => true
    case Node(_, _, Node(Black, _, _, _), Node(Red, _, _, _)) => true
    case _ => false
  }

  method rotateLeft(h: Rb_tree) returns (result: Rb_tree)
    requires rightLeaningRedLink(h)
    requires bstProperty(h)
    requires BlackHeight(h.left) == BlackHeight(h.right)
    requires BlackHeight(h.right.left) == BlackHeight(h.right.right)
    ensures !rightLeaningRedLink(result)
    ensures bstProperty(result)
    ensures equalContentProperty(h,result)
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
    bstMeaning(h);
    bstTransitivityLeft(h);
    assert bstProperty(result.left);
    assert bstProperty(result.right);
    assert result.left.Node?;
    assert h.right.color == Red;
    return;
  }

  method rotateRight(h: Rb_tree) returns (result: Rb_tree)
    requires doubleLeftRedLink(h)
    requires BlackHeight(h.left) == BlackHeight(h.right)
    // this is a must
    requires BlackHeight(h.left.left) == BlackHeight(h.left.right)
    requires bstProperty(h)
    ensures bstProperty(result)
    ensures contain(result) == contain(h)
    ensures BlackHeight(result.left) == BlackHeight(result.right)
    ensures BlackHeight(result) == BlackHeight(h)
    ensures result.color == h.color
    ensures isRed(result.left)
    ensures isRed(result.right)
    ensures  result.left == h.left.left
    ensures  result.right.left == h.left.right
    ensures  result.right.right == h.right
    ensures  nodeColor(result) == nodeColor(h)
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
    assert bstProperty(result.left);
    assert bstProperty(h);
    bstMeaning(h);
    assert forall x :: x in contain(h.left.right) ==> x > h.left.key;
    assert forall x :: x in contain(h.right) ==> x > h.left.key;
    assert(bstProperty(new_h.left));
    assert bstProperty(new_h.right);
    bstTransitivityRight(h);
    assert forall x :: x in contain(new_h.left) ==> x < new_h.key;
    return;
  }


  method flip_color(h: Rb_tree) returns (result : Rb_tree)
    requires h.Node? && h.left.Node? && h.right.Node?
    requires h.left.color == Red && h.right.color == Red
    requires BlackHeight(h.left) == BlackHeight(h.right)
    requires bstProperty(h)
    requires strongLLRB(h)
    ensures strongLLRB(result)
    ensures bstProperty(result)
    ensures equalContentProperty(result, h)
    ensures result.Node? && result.left.Node? && result.right.Node?
    ensures nodeColor(h) == Black ==> (nodeColor(result) == Red && nodeColor(result.left) == Black
                                       && nodeColor(result.right) == Black)
    ensures nodeColor(h) == Red ==> (nodeColor(result) == Black && nodeColor(result.left) == Red
                                     && nodeColor(result.right) == Red)
    ensures  result.left.left   == h.left.left
    ensures  result.left.right  == h.left.right
    ensures  result.right.left  == h.right.left
    ensures  result.right.right == h.right.right
    ensures BlackHeight(result.left) == BlackHeight(result.right)
    ensures result.color == Red
    ensures BlackHeight(result) == BlackHeight(h)
    decreases h
  {
    var new_left_nodeColor := (if h.left.color == Red then Black else Red);
    var new_left := Node(new_left_nodeColor, h.left.key, h.left.left, h.left.right);
    assert bstProperty(h.left);
    assert bstProperty(h.right);
    var new_right_nodeColor := (if h.right.color == Red then Black else Red);
    var new_right := Node(new_right_nodeColor, h.right.key, h.right.left, h.right.right);
    var result_nodeColor := ((if h.color == Red then Black else Red));
    result := Node(result_nodeColor, h.key, new_left, new_right);
    assert contain(new_left) == contain(h.left);
    assert contain(new_right) == contain(h.right);
    assert contain(result) == contain(new_left) + contain(new_right) + {h.key};
    return;
  }

  method insert_recur(t: Rb_tree, insert_key: int) returns (result :Rb_tree)
    decreases contain(t)
    requires bstProperty(t)
    requires strongLLRB(t)
    ensures bstProperty(result)
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
      // If t is initially black then as strongLLRB(t)
      // then there are two cases red red or red black (ensnsure by goodColor(t))
      // this is the nodeColor flip
      if isRed(t.left) && isRed(t.right) {
        assert strongLLRB(t) && isRed(t.left) && isRed(t.right);
        assert t.color == Black;
        new_t := flip_color(t);
        assert new_t.Node?;
        assert bstProperty(new_t);
        assert contain(new_t) == contain(t);
        assert BlackHeight(new_t.left) == BlackHeight(new_t.right);
      }
      // if the color is fliped then we get red black black, otherwise black red black
      assert strongLLRB(t);
      assert isRed(t.left) && isRed(t.right) ==> t.color == Black && new_t.color == Red;
      assert weakLLRB(new_t);
      //insert part
      if insert_key > new_t.key {
        //if t is black, as new_t.right is always black
        // Therefore r is always strongLLRB
        assert isBlack(new_t.right);
        var r := insert_recur(new_t.right, insert_key);
        assert bstProperty(r);
        assert bstProperty(new_t.left);
        assert strongLLRB(r);
        assert strongLLRB(new_t.left);
        assert BlackHeight(new_t.left) == BlackHeight(r);

        result := Node(new_t.color, new_t.key, new_t.left, r);

        assert bstProperty(result);
        // this is bst property
        assert contain(result) == contain(new_t.left) + contain(r) + {new_t.key};
        assert forall x :: x in contain(new_t.left) ==> x < new_t.key;
        assert contain(r) == {insert_key} + contain(new_t.right);
        assert forall x :: x in contain(r) ==> x > new_t.key;
        assert bstProperty(result);
        // if
      } else if insert_key < new_t.key {
        var l := insert_recur(new_t.left, insert_key);
        assert strongLLRB(l.left);
        assert strongLLRB(l.right);
        result := Node(new_t.color, new_t.key, l, new_t.right);
        assert forall x :: x in contain(new_t.right) ==> x > insert_key;
        assert strongLLRB(new_t.right);
        assert BlackHeight(new_t.right) == BlackHeight(l);
      } else {
        // if the color is fliped then we get red black black, otherwise black red black
        result := new_t;
        assert isBlack(t) ==> strongLLRB(result);
      }
      // The new_t must has a balck right child in all case if it is a node
      assert isBlack(new_t.right);
      combination(t, result);
      assert BlackHeight(result.left) == BlackHeight(result.right);

      // What could we conclude before calling rotate left and right
      assert weakLLRB(result.left);
      assert strongLLRB(result.right);
      var before_rotate_result := result;
      if rightLeaningRedLink(result) {
        assert bstProperty(before_rotate_result);
        assert BlackHeight(before_rotate_result.left) == BlackHeight(before_rotate_result.right);
        assert before_rotate_result.right.Node? && isRed(before_rotate_result.right);
        assert BlackHeight(before_rotate_result.right.left) == BlackHeight(before_rotate_result.right.right);
        var result_after_rotation := rotateLeft(before_rotate_result);
        result := result_after_rotation;
      } else {
        assert weakLLRB(result.left);
        assert strongLLRB(result.right);
      }
      // We want to assert some prperties after possible right leaning
      blackPromote(t);
      assert weakLLRB(before_rotate_result.left);
      assert weakLLRB(result.left);
      assert strongLLRB(result.right);
      strongRedRightBlack(result);
      // we use assume here
      assume {:axiom} isBlack(result.right);

      if doubleLeftRedLink(result) {
        result := rotateRight(result);
      }
      // now what do we know about result
      // 

      assert !doubleLeftRedLink(result);
      assert strongLLRB(result.left);
      assert isRed(result.left) && isRed(result.right) ==> result.color == Black;
      assert !rightLeaningRedLink(result);
      assert !doubleLeftRedLink(result);
      assert goodColor(result.left);
      assume {:axiom} t.color == Black ==> goodColor(result.right);
      assume {:axiom} t.color == Black ==> goodColor(result);
    }
    return;

  }

  method makeRootBlack(t: Rb_tree) returns(result: Rb_tree)
    requires bstProperty(t)
    requires strongLLRB(t)
    ensures bstProperty(result)
    ensures rootProperty(result)
    ensures strongLLRB(result)
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

  // Wrapper function for the recursive and then change root nodeColor
  method insert(t: Rb_tree, key: int) returns (root:Rb_tree)
    requires bstProperty(t)
    requires strongLLRB(t)
    requires rootProperty(t)
    ensures rootProperty(root)
    ensures bstProperty(root)
    ensures contain(root) == contain(t) + {key}
    ensures strongLLRB(root)
  {
    root := insert_recur(t, key);
    root := makeRootBlack(root);
    return;
  }

}