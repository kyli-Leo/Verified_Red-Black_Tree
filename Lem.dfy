include "Type.dfy"
include "Property.dfy"
module Lem {
  import opened Type
  import opened Property

  function makeRootBlack(t: Rb_tree): Rb_tree
  {
    match t
    case Node(_, k, l, r) => Node(Black, k, l, r)
    case Null => Null
  }

  lemma lem_make_black (t:Rb_tree)
    ensures root_property2(makeRootBlack(t)) {
  }

  lemma bst_meaning(t:Rb_tree)
    requires t.Node? &&t.left.Node? && t.right.Node? && bst_property(t)
    ensures t.left.key < t.key
    ensures t.right.key > t.key
  {
    assert t.left.key in contain(t.left);
    assert forall x :: x in contain(t.left) ==> x < t.key;
    assert t.left.key < t.key;

    assert t.right.key in contain(t.right);
    assert forall x :: x in contain(t.right) ==> x > t.key;
    assert t.right.key > t.key;
  }
  lemma bst_transitivity_right(t:Rb_tree)
    requires t.Node? &&t.left.Node? && t.right.Node? && bst_property(t)
    ensures forall x :: x in contain (t.left.right)==> x < t.key

  {
    assert bst_property(t);
    assert bst_property(t.left);
    assert bst_property(t.right);
    assert forall x :: x in contain(t.left.right) ==> x in contain(t.left);

  }
}