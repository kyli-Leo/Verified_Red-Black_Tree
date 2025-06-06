import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_
import Type as Type

# Module: Property

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def rootProperty(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_nodeColor_ = source0_.color
            return (d_0_nodeColor_) == (Type.Color_Black())

    @staticmethod
    def nodeColor(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return Type.Color_Black()
        if True:
            d_0_c_ = source0_.color
            return d_0_c_

    @staticmethod
    def Max(left, right):
        if (left) >= (right):
            return left
        elif True:
            return right

    @staticmethod
    def BlackHeight(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return 1
        if True:
            d_0_nodeColor_ = source0_.color
            d_1_left_ = source0_.left
            d_2_right_ = source0_.right
            d_3_leftHeight_ = default__.BlackHeight(d_1_left_)
            d_4_rightHeight_ = default__.BlackHeight(d_2_right_)
            d_5_result_ = default__.Max(d_3_leftHeight_, d_4_rightHeight_)
            if (d_0_nodeColor_) == (Type.Color_Black()):
                return (d_5_result_) + (1)
            elif True:
                return d_5_result_

    @staticmethod
    def contain(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return _dafny.Set({})
        if True:
            d_0_key_ = source0_.key
            d_1_left_ = source0_.left
            d_2_right_ = source0_.right
            return ((_dafny.Set({d_0_key_})) | (default__.contain(d_1_left_))) | (default__.contain(d_2_right_))

    @staticmethod
    def bstProperty(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_key_ = source0_.key
            d_1_left_ = source0_.left
            d_2_right_ = source0_.right
            def lambda0_(forall_var_0_):
                d_3_x_: int = forall_var_0_
                return not ((d_3_x_) in (default__.contain(d_1_left_))) or ((d_3_x_) < (d_0_key_))

            def lambda1_(forall_var_1_):
                d_4_y_: int = forall_var_1_
                return not ((d_4_y_) in (default__.contain(d_2_right_))) or ((d_4_y_) > (d_0_key_))

            return (((default__.bstProperty(d_1_left_)) and (default__.bstProperty(d_2_right_))) and (_dafny.quantifier((default__.contain(d_1_left_)).Elements, True, lambda0_))) and (_dafny.quantifier((default__.contain(d_2_right_)).Elements, True, lambda1_))

    @staticmethod
    def equalContentProperty(t1, t2):
        return (default__.contain(t1)) == (default__.contain(t2))

    @staticmethod
    def isRed(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return False
        if True:
            d_0_nodeColor_ = source0_.color
            return (d_0_nodeColor_) == (Type.Color_Red())

    @staticmethod
    def isBlack(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_nodeColor_ = source0_.color
            return (d_0_nodeColor_) == (Type.Color_Black())

    @staticmethod
    def doubleLeftRedLink(h):
        source0_ = h
        if True:
            if source0_.is_Node:
                d_0_h__nodeColor_ = source0_.color
                d_1_h__key_ = source0_.key
                left0 = source0_.left
                if left0.is_Node:
                    color0 = left0.color
                    if color0.is_Red:
                        d_2_x__key_ = left0.key
                        left1 = left0.left
                        if left1.is_Node:
                            color1 = left1.color
                            if color1.is_Red:
                                return True
        if True:
            return False

    @staticmethod
    def goodColor(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_c_ = source0_.color
            d_1_l_ = source0_.left
            d_2_r_ = source0_.right
            if (d_0_c_) == (Type.Color_Red()):
                return ((default__.nodeColor(d_1_l_)) == (Type.Color_Black())) and ((default__.nodeColor(d_2_r_)) == (Type.Color_Black()))
            elif True:
                return not ((default__.nodeColor(d_2_r_)) == (Type.Color_Red())) or ((default__.nodeColor(d_1_l_)) == (Type.Color_Red()))

    @staticmethod
    def rightLeaningRedLink(t):
        source0_ = t
        if True:
            if source0_.is_Node:
                left0 = source0_.left
                if left0.is_Null:
                    right0 = source0_.right
                    if right0.is_Node:
                        color0 = right0.color
                        if color0.is_Red:
                            return True
        if True:
            if source0_.is_Node:
                left1 = source0_.left
                if left1.is_Node:
                    color1 = left1.color
                    if color1.is_Black:
                        right1 = source0_.right
                        if right1.is_Node:
                            color2 = right1.color
                            if color2.is_Red:
                                return True
        if True:
            return False

    @staticmethod
    def strongLLRB(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_c_ = source0_.color
            d_1_k_ = source0_.key
            d_2_l_ = source0_.left
            d_3_r_ = source0_.right
            return ((((default__.strongLLRB(d_2_l_)) and (default__.strongLLRB(d_3_r_))) and ((default__.BlackHeight(d_2_l_)) == (default__.BlackHeight(d_3_r_)))) and (default__.bstProperty(t))) and (default__.goodColor(t))

    @staticmethod
    def weakLLRB(t):
        source0_ = t
        if True:
            if source0_.is_Null:
                return True
        if True:
            d_0_c_ = source0_.color
            d_1_k_ = source0_.key
            d_2_l_ = source0_.left
            d_3_r_ = source0_.right
            return ((((default__.strongLLRB(d_2_l_)) and (default__.strongLLRB(d_3_r_))) and ((default__.BlackHeight(d_2_l_)) == (default__.BlackHeight(d_3_r_)))) and (default__.bstProperty(t))) and (not ((default__.nodeColor(d_3_r_)) == (Type.Color_Red())) or ((default__.nodeColor(d_2_l_)) == (Type.Color_Red())))

