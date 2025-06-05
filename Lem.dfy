include "Type.dfy"
include "Property.dfy"
module Lem {
  import opened Type
  import opened Property

  lemma bstMeaning(t:Rb_tree)
    requires t.Node? && bstProperty(t)
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
  lemma bstTransitivityRight(t:Rb_tree)
    requires t.Node? &&t.left.Node? && bstProperty(t)
    ensures forall x :: x in contain (t.left.right)==> x < t.key

  {
    assert bstProperty(t);
    assert bstProperty(t.left);
    assert bstProperty(t.right);
    assert forall x :: x in contain(t.left.right) ==> x in contain(t.left);

  }

  lemma bstTransitivityLeft(t:Rb_tree)
    requires t.Node? && t.right.Node? && bstProperty(t)
    ensures forall x :: x in contain (t.right.left)==> x > t.key

  {
    assert bstProperty(t);
    assert bstProperty(t.right);
    assert bstProperty(t.left);
    assert forall x :: x in contain(t.right.left) ==> x in contain(t.right);
  }

  lemma strongVsWeak(t:Rb_tree)
    requires strongLLRB(t)
    ensures weakLLRB(t)

  {}

  lemma combination(input :Rb_tree, output: Rb_tree)
    ensures (isBlack(input) ==> strongLLRB(output)) && (!isBlack(input) ==> weakLLRB(output)) ==> weakLLRB(output)
  {
  }


  lemma blackPromote(t: Rb_tree)
    ensures (isBlack(t) && weakLLRB(t)) ==> strongLLRB(t)
  {
  }

  lemma promote_to_strong(n: Rb_tree, l_child: Rb_tree, r_child: Rb_tree)
    requires n.Node? && n.left == l_child && n.right == r_child
    requires isBlack(n)
    requires l_child.Null? || (isBlack(l_child) && strongLLRB(l_child))
    requires r_child.Null? || (isBlack(r_child) && strongLLRB(r_child))
    requires BlackHeight(l_child) == BlackHeight(r_child)
    requires bstProperty(n)
    ensures strongLLRB(n)
  {
  }

  lemma color_dont_change_bst(t_orig: Rb_tree, new_color: Color)
    requires t_orig.Node?
    requires bstProperty(t_orig)
    ensures bstProperty(Node(new_color, t_orig.key, t_orig.left, t_orig.right))
    ensures contain(Node(new_color, t_orig.key, t_orig.left, t_orig.right)) == contain(t_orig)
  {
  }

  lemma strongRedRightBlack (t: Rb_tree)
    ensures (strongLLRB(t) && isRed(t)) ==> isBlack(t.right)
  {

  }
}