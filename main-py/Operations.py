import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Type as Type
import Property as Property
import Lem as Lem

# Module: Operations

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def rotateLeft(h):
        result: Type.Rb__tree = Type.Rb__tree.default()()
        d_0_new__h_: Type.Rb__tree
        d_0_new__h_ = Type.Rb__tree_Node(Type.Color_Red(), (h).key, (h).left, ((h).right).left)
        result = Type.Rb__tree_Node((h).color, ((h).right).key, d_0_new__h_, ((h).right).right)
        return result
        return result

    @staticmethod
    def rotateRight(h):
        result: Type.Rb__tree = Type.Rb__tree.default()()
        d_0_new__h_: Type.Rb__tree
        d_0_new__h_ = Type.Rb__tree_Node(Type.Color_Red(), (h).key, ((h).left).right, (h).right)
        result = Type.Rb__tree_Node((h).color, ((h).left).key, ((h).left).left, d_0_new__h_)
        return result
        return result

    @staticmethod
    def flip__color(h):
        result: Type.Rb__tree = Type.Rb__tree.default()()
        d_0_new__left__nodeColor_: Type.Color
        if (((h).left).color) == (Type.Color_Red()):
            d_0_new__left__nodeColor_ = Type.Color_Black()
        elif True:
            d_0_new__left__nodeColor_ = Type.Color_Red()
        d_1_new__left_: Type.Rb__tree
        d_1_new__left_ = Type.Rb__tree_Node(d_0_new__left__nodeColor_, ((h).left).key, ((h).left).left, ((h).left).right)
        d_2_new__right__nodeColor_: Type.Color
        if (((h).right).color) == (Type.Color_Red()):
            d_2_new__right__nodeColor_ = Type.Color_Black()
        elif True:
            d_2_new__right__nodeColor_ = Type.Color_Red()
        d_3_new__right_: Type.Rb__tree
        d_3_new__right_ = Type.Rb__tree_Node(d_2_new__right__nodeColor_, ((h).right).key, ((h).right).left, ((h).right).right)
        d_4_result__nodeColor_: Type.Color
        if ((h).color) == (Type.Color_Red()):
            d_4_result__nodeColor_ = Type.Color_Black()
        elif True:
            d_4_result__nodeColor_ = Type.Color_Red()
        result = Type.Rb__tree_Node(d_4_result__nodeColor_, (h).key, d_1_new__left_, d_3_new__right_)
        return result
        return result

    @staticmethod
    def insert__recur(t, insert__key):
        result: Type.Rb__tree = Type.Rb__tree.default()()
        if (t).is_Null:
            result = Type.Rb__tree_Node(Type.Color_Red(), insert__key, Type.Rb__tree_Null(), Type.Rb__tree_Null())
            return result
        elif True:
            d_0_new__t_: Type.Rb__tree
            d_0_new__t_ = t
            if (Property.default__.isRed((t).left)) and (Property.default__.isRed((t).right)):
                out0_: Type.Rb__tree
                out0_ = default__.flip__color(t)
                d_0_new__t_ = out0_
            if (insert__key) > ((d_0_new__t_).key):
                d_1_r_: Type.Rb__tree
                out1_: Type.Rb__tree
                out1_ = default__.insert__recur((d_0_new__t_).right, insert__key)
                d_1_r_ = out1_
                result = Type.Rb__tree_Node((d_0_new__t_).color, (d_0_new__t_).key, (d_0_new__t_).left, d_1_r_)
            elif (insert__key) < ((d_0_new__t_).key):
                d_2_l_: Type.Rb__tree
                out2_: Type.Rb__tree
                out2_ = default__.insert__recur((d_0_new__t_).left, insert__key)
                d_2_l_ = out2_
                result = Type.Rb__tree_Node((d_0_new__t_).color, (d_0_new__t_).key, d_2_l_, (d_0_new__t_).right)
            elif True:
                result = d_0_new__t_
            d_3_before__rotate__result_: Type.Rb__tree
            d_3_before__rotate__result_ = result
            if Property.default__.rightLeaningRedLink(result):
                d_4_result__after__rotation_: Type.Rb__tree
                out3_: Type.Rb__tree
                out3_ = default__.rotateLeft(d_3_before__rotate__result_)
                d_4_result__after__rotation_ = out3_
                result = d_4_result__after__rotation_
            elif True:
                pass
            if Property.default__.doubleLeftRedLink(result):
                out4_: Type.Rb__tree
                out4_ = default__.rotateRight(result)
                result = out4_
        return result
        return result

    @staticmethod
    def makeRootBlack(t):
        result: Type.Rb__tree = Type.Rb__tree.default()()
        if (t).is_Node:
            result = Type.Rb__tree_Node(Type.Color_Black(), (t).key, (t).left, (t).right)
        elif True:
            result = Type.Rb__tree_Null()
        return result
        return result

    @staticmethod
    def insert(t, key):
        root: Type.Rb__tree = Type.Rb__tree.default()()
        out0_: Type.Rb__tree
        out0_ = default__.insert__recur(t, key)
        root = out0_
        out1_: Type.Rb__tree
        out1_ = default__.makeRootBlack(root)
        root = out1_
        return root
        return root

