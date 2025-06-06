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
import Operations as Operations

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Pad(n):
        d_0___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " ")))
                    in0_ = (n) - (1)
                    n = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def PrintTree(t, indent):
        if (t) == (Type.Rb__tree_Null()):
            _dafny.print((default__.Pad(indent)).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "·\n"))).VerbatimString(False))
        elif True:
            default__.PrintTree((t).right, (indent) + (4))
            _dafny.print((default__.Pad(indent)).VerbatimString(False))
            _dafny.print(((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "R")) if ((t).color) == (Type.Color_Red()) else _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "B")))).VerbatimString(False))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "("))).VerbatimString(False))
            _dafny.print(_dafny.string_of((t).key))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, ")\n"))).VerbatimString(False))
            default__.PrintTree((t).left, (indent) + (4))

    @staticmethod
    def Main(noArgsParameter__):
        d_0_t_: Type.Rb__tree
        d_0_t_ = Type.Rb__tree_Null()
        d_1_keys_: _dafny.Seq
        d_1_keys_ = _dafny.SeqWithoutIsStrInference([10, 7, 18, 2, 8, 15, 25, 1, 3])
        d_2_i_: int
        d_2_i_ = 0
        while (d_2_i_) < (len(d_1_keys_)):
            out0_: Type.Rb__tree
            out0_ = Operations.default__.insert(d_0_t_, (d_1_keys_)[d_2_i_])
            d_0_t_ = out0_
            d_2_i_ = (d_2_i_) + (1)
        _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "RedBlack tree after inserts:\n"))).VerbatimString(False))
        default__.PrintTree(d_0_t_, 0)

