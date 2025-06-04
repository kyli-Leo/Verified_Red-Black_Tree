include "Type.dfy"
include "Property.dfy"
module Lem {
  import opened Type
  import opened Property

  lemma bst_meaning(t:RbTree)
    requires t.Node? && is_bst(t)
    ensures !t.left.Node? || t.left.key < t.key
    ensures !t.right.Node? || t.right.key > t.key
  {
    // assert t.left.key in contain(t.left);
    assert forall x :: x in contain(t.left) ==> x < t.key;
    //assert t.left.key < t.key;

    //assert t.right.key in contain(t.right);
    assert forall x :: x in contain(t.right) ==> x > t.key;
    // assert t.right.key > t.key;
  }
  lemma bst_transitivity_right(t:RbTree)
    requires t.Node? &&t.left.Node? && is_bst(t)
    ensures forall x :: x in contain (t.left.right)==> x < t.key

  {
    assert is_bst(t);
    assert is_bst(t.left);
    assert is_bst(t.right);
    assert forall x :: x in contain(t.left.right) ==> x in contain(t.left);

  }

  lemma bst_transitivity_left(t:RbTree)
    requires t.Node? && t.right.Node? && is_bst(t)
    ensures forall x :: x in contain (t.right.left)==> x > t.key

  {
    assert is_bst(t);
    assert is_bst(t.right);
    assert is_bst(t.left);
    assert forall x :: x in contain(t.right.left) ==> x in contain(t.right);
  }


}