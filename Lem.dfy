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

  lemma strongVsWeak(t:Rb_tree)
    requires strongLLRB(t)
    ensures weakLLRB(t)

  {}

  lemma combination(input :Rb_tree, output: Rb_tree)
    ensures (isBlack(input) ==> strongLLRB(output)) && (!isBlack(input) ==> weakLLRB(output)) ==> weakLLRB(output)
  {
  }

  // lemma {:axiom} DLL_Contradicts_WeakLLRB_Child(h_node: Rb_tree)
  //   requires h_node.Node? && h_node.left.Node?
  //   requires weakLLRB(h_node.left) // If h.left was l_rec directly
  //   requires double_left_red_link(h_node)
  //   ensures false
  // {
  //   var N := h_node.left; // N is l_rec
  //   assert N.color == Red; // From double_left_red_link(h_node)
  //   assert N.left.Node? && N.left.color == Red; // From double_left_red_link(h_node)
  //   // weakLLRB(N) implies goodColor(N).
  //   // goodColor(N) when N is Red implies N.left is Black.
  //   // This establishes the contradiction. Unfold definitions if necessary.
  //   if N.Node? && N.color == Red && weakLLRB(N) { // Trigger unfolding of weakLLRB
  //     assert N.Node? && N.color == Red && strongLLRB(N.left);
  //     assume nodeColor(N.left) == Black; // By goodColor part of weakLLRB(N)
  //   }
  //   // Now we have N.left.color == Red and N.left.color == Black
  //   assert N.left.color == Black && N.left.color == Red; // Should lead to false
  // }

  lemma black_promote(t: Rb_tree)
    ensures (isBlack(t) && weakLLRB(t)) ==> strongLLRB(t)
  {
  }

  lemma promote_to_strong(n: Rb_tree, l_child: Rb_tree, r_child: Rb_tree)
    requires n.Node? && n.left == l_child && n.right == r_child
    requires isBlack(n)
    requires l_child.Null? || (isBlack(l_child) && strongLLRB(l_child))
    requires r_child.Null? || (isBlack(r_child) && strongLLRB(r_child))
    requires BlackHeight(l_child) == BlackHeight(r_child)
    requires bst_property(n)
    ensures strongLLRB(n)
  {
  }

  lemma color_dont_change_color(t_orig: Rb_tree, new_color: Color)
    requires t_orig.Node?
    requires bst_property(t_orig)
    ensures bst_property(Node(new_color, t_orig.key, t_orig.left, t_orig.right))
    ensures contain(Node(new_color, t_orig.key, t_orig.left, t_orig.right)) == contain(t_orig)
  {
    var t_new := Node(new_color, t_orig.key, t_orig.left, t_orig.right);
  }
}