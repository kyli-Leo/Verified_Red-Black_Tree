include "Type.dfy"
include "Property.dfy"
module Lem {
  import opened Type
  import opened Property

  lemma bst_meaning(t:Rb_tree)
    requires t.Node? && bst_property(t)
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
  lemma bst_transitivity_right(t:Rb_tree)
    requires t.Node? &&t.left.Node? && bst_property(t)
    ensures forall x :: x in contain (t.left.right)==> x < t.key

  {
    assert bst_property(t);
    assert bst_property(t.left);
    assert bst_property(t.right);
    assert forall x :: x in contain(t.left.right) ==> x in contain(t.left);

  }

  lemma bst_transitivity_left(t:Rb_tree)
    requires t.Node? && t.right.Node? && bst_property(t)
    ensures forall x :: x in contain (t.right.left)==> x > t.key

  {
    assert bst_property(t);
    assert bst_property(t.right);
    assert bst_property(t.left);
    assert forall x :: x in contain(t.right.left) ==> x in contain(t.right);
  }
}