module Type {
  // class Node {
  //   var key: int
  //   var color: bool // true = RED, false = BLACK
  //   var left: Node?
  //   var right: Node?
  //   var parent: Node?


  //   constructor(k: int) {
  //     key := k;
  //     color := true;
  //     left := null;
  //     right := null;
  //     parent := null;
  //   }
  // }

  // class RedBlackTree {
  //   var root: Node?

  // }
  datatype Color = Red | Black
  datatype Rb_tree = Null | Node(color: Color, key: int, left: Rb_tree, right: Rb_tree)
}


