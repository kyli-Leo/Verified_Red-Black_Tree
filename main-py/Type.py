import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: Type


class Color:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Color_Red(), Color_Black()]
    @classmethod
    def default(cls, ):
        return lambda: Color_Red()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Red(self) -> bool:
        return isinstance(self, Color_Red)
    @property
    def is_Black(self) -> bool:
        return isinstance(self, Color_Black)

class Color_Red(Color, NamedTuple('Red', [])):
    def __dafnystr__(self) -> str:
        return f'Type.Color.Red'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Color_Red)
    def __hash__(self) -> int:
        return super().__hash__()

class Color_Black(Color, NamedTuple('Black', [])):
    def __dafnystr__(self) -> str:
        return f'Type.Color.Black'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Color_Black)
    def __hash__(self) -> int:
        return super().__hash__()


class Rb__tree:
    @classmethod
    def default(cls, ):
        return lambda: Rb__tree_Null()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Null(self) -> bool:
        return isinstance(self, Rb__tree_Null)
    @property
    def is_Node(self) -> bool:
        return isinstance(self, Rb__tree_Node)

class Rb__tree_Null(Rb__tree, NamedTuple('Null', [])):
    def __dafnystr__(self) -> str:
        return f'Type.Rb_tree.Null'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Rb__tree_Null)
    def __hash__(self) -> int:
        return super().__hash__()

class Rb__tree_Node(Rb__tree, NamedTuple('Node', [('color', Any), ('key', Any), ('left', Any), ('right', Any)])):
    def __dafnystr__(self) -> str:
        return f'Type.Rb_tree.Node({_dafny.string_of(self.color)}, {_dafny.string_of(self.key)}, {_dafny.string_of(self.left)}, {_dafny.string_of(self.right)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Rb__tree_Node) and self.color == __o.color and self.key == __o.key and self.left == __o.left and self.right == __o.right
    def __hash__(self) -> int:
        return super().__hash__()

