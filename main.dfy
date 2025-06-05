include "Type.dfy"
include "Property.dfy"
include "Operations.dfy"

module Main {
  import opened Type
  import opened Operations
  import opened Property

  function Pad(n: nat): string
    decreases n
  {
    if n == 0 then "" else " " + Pad(n - 1)
  }
  method PrintTree(t: Rb_tree, indent: nat := 0)
    decreases t
  {
    if t == Null {
      print Pad(indent); print "·\n";
    } else {
      PrintTree(t.right, indent + 4);
      print Pad(indent);
      print (if t.color == Red then "R" else "B");
      print "("; print t.key; print ")\n";
      PrintTree(t.left, indent + 4);
    }
  }
  method {:main} Main() {
    var t := Null;
    var keys := [10, 7, 18, 2, 8, 15, 25, 1, 3];
    var i := 0;
    while i < |keys|
      invariant 0 <= i <= |keys|
      invariant bstProperty(t)
      invariant strongLLRB(t)
      invariant rootProperty(t)
      decreases |keys| - i
    {
      t := insert(t, keys[i]);
      i := i + 1;
    }
    print "RedBlack tree after inserts:\n";
    PrintTree(t);
  }
}