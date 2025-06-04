include "Type.dfy"
include "Property.dfy"
include "Lem.dfy"
module Operations {
  import opened Type
  import opened Property
  import opened Lem

  method Balance(node_color: Color, k_node: int, l_child: RbTree, r_child: RbTree) returns (balanced_node: RbTree)
    requires IsRbSubTree(l_child) && IsRbSubTree(r_child)
    requires l_child.Null? || r_child.Null? || BlackHeight(l_child) == BlackHeight(r_child) // If both non-empty
    requires bst_property(k_node, l_child, r_child)
    ensures IsRbSubTree(balanced_node)
    // A key ensure for Okasaki's balance when it fixes B(R(R,..)) is that balanced_node.color == Red
    // and its children are Black and have a black-height such that the overall path black-height is preserved.
    // More specific ensures about color and structure would be needed.
  {
    // Case 1: Black parent, left-left Red violation
    // B( R(R(a,xl,b), x, c), y, d)  => R( B(a,xl,b), x, B(c,y,d) )
    if node_color == Black && l_child.Node? && GetColor(l_child) == Red && l_child.left.Node? && GetColor(l_child.left) == Red {
      // l_child = Node(Red, l_child.left, l_child.key, l_child.right)
      // l_child.left = Node(Red, l_child.left.left, l_child.left.key, l_child.left.right)
      var ll_grandchild := l_child.left; // This is the R(a,xl,b) part
      // Reconstruct as: Red( Black(ll_grandchild.left, ll_grandchild.key, ll_grandchild.right),
      //                      l_child.key,
      //                      Black(l_child.right, k_node, r_child) )
      return Node(Red,l_child.key,
                  Node(Black, ll_grandchild.key, ll_grandchild.left, ll_grandchild.right),
                  Node(Black, k_node, l_child.right, r_child));
    }
    // Case 2: Black parent, left-right Red violation
    // B( R(a,x,R(b,y,c)), z, d) => R( B(a,x,b), y, B(c,z,d) )
    else if node_color == Black &&
            l_child.Node? && GetColor(l_child) == Red &&
            l_child.right.Node? && GetColor(l_child.right) == Red {
      // l_child = Node(Red, l_child.left, l_child.key, l_child.right)
      // l_child.right = Node(Red, l_child.right.left, l_child.right.key, l_child.right.right)
      var lr_grandchild := l_child.right; // This is the R(b,y,c) part
      // Reconstruct as: Red( Black(l_child.left, l_child.key, lr_grandchild.left),
      //                      lr_grandchild.key,
      //                      Black(lr_grandchild.right, k_node, r_child) )
      return Node(Red,
                  lr_grandchild.key,
                  Node(Black, l_child.key, l_child.left, lr_grandchild.left),
                  Node(Black, k_node, lr_grandchild.right, r_child));
    }
    // Case 3: Black parent, right-left Red violation (symmetric to Case 2)
    // B( a,x,R(R(b,y,c),z,d) ) => R( B(a,x,b), y, B(c,z,d) )
    else if node_color == Black &&
            r_child.Node? && GetColor(r_child) == Red &&
            r_child.left.Node? && GetColor(r_child.left) == Red {
      var rl_grandchild := r_child.left; // This is the R(b,y,c) part
      // Reconstruct as: Red( Black(l_child, k_node, rl_grandchild.left),
      //                      rl_grandchild.key,
      //                      Black(rl_grandchild.right, r_child.key, r_child.right) )
      return Node(Red,rl_grandchild.key, Node(Black,k_node, l_child,  rl_grandchild.left),
                  Node(Black, r_child.key,  rl_grandchild.right, r_child.right));
    }
    // Case 4: Black parent, right-right Red violation (symmetric to Case 1)
    // B( a,x,R(b,y,R(c,z,d)) ) => R( B(a,x,b), y, B(c,z,d) )
    else if node_color == Black &&
            r_child.Node? && GetColor(r_child) == Red &&
            r_child.right.Node? && GetColor(r_child.right) == Red {
      var rr_grandchild := r_child.right; // This is the R(c,z,d) part
      // Reconstruct as: Red( Black(l_child, k_node, r_child.left),
      //                      r_child.key,
      //                      Black(rr_grandchild.left, rr_grandchild.key, rr_grandchild.right) )
      return Node(Red, r_child.key, Node(Black, k_node, l_child, r_child.left),
                  Node(Black,rr_grandchild.key, rr_grandchild.left, rr_grandchild.right));
    }
    // Default case: No specific Red-Red pattern matched, or parent `node_color` was Red.
    // Just reconstruct with original colors (or colors from children).
    else {
      var defaultNode := Node(node_color, k_node, l_child, r_child);
      assert noRedRedViolation(defaultNode);
      return defaultNode;
    }
  }

  method InsertRecur(t: RbTree, ins_key: int)
    returns (result: RbTree)
    requires IsRbSubTree(t) // Input subtree is valid (root can be red)

    ensures IsRbSubTree(result) // Output subtree is valid
    ensures result.Node? // New node is always inserted if key not present
    // Ensures that if a Red-Red violation was created by inserting 'ins_key' as Red,
    // 'result' (after balance) will have fixed it locally, possibly by making result.color Red.
    // Ensures black-height is maintained correctly (this is hard).
    // For Okasaki, BH(Balance(c,l,k,r)) should relate to BH of original Node(c,l_orig,k,r_orig)
    ensures contain(result) == contain(t) + {ins_key}
    // Ensures that the color of the returned node 'result' is such that its parent (if any)
    // can then call Balance on itself. If 'result' is Red, its children must be Black.
    // This is implicitly part of IsRbSubTree(result) -> NoRedRedViolation(result).
    decreases t // Dafny needs a decreases measure for recursion
  {
    if t.Null? {
      result := Node(Red, ins_key, Null, Null); // New nodes are Red
    } else {
      var Node(c, k, l, r) := t;
      if ins_key < k {
        var new_l := InsertRecur(l, ins_key);
        result := Balance(c, k, new_l, r);
      } else if ins_key > k {
        var new_r := InsertRecur(r, ins_key);
        result := Balance(c, k, l, new_r);
      } else {
        result := Node(c, k, l, r);
      }
    }
  }
}