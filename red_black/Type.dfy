module Type {
  // class NodeC {
  //   var key: int
  //   var color: bool // true == RED, false == BLACK
  //   var index: nat
  //   constructor(k: int, idx: nat) {
  //     key := k;
  //     index := idx;
  //     color := true;
  //   }
  // }

  // class RedBlackTree {
  //   var arr : array<NodeC>
  // }

  datatype Color = Red | Black
  datatype RbTree = Null | Node(color: Color, key: int, left: RbTree, right: RbTree)
}


