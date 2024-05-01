import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Pos
import DafnyVMCPartMaterial
import NatArith
import RealArith
import Reals
import Sequences
import Limits
import Series
import Measures

# Module: Rand

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Head(s):
        return s(0)

    @staticmethod
    def Tail(s):
        def lambda12_(d_21_s_):
            def lambda13_(d_22_n_):
                return d_21_s_((d_22_n_) + (1))

            return lambda13_

        return lambda12_(s)

    @staticmethod
    def IterateTail(s, n):
        while True:
            with _dafny.label():
                if (n) == (0):
                    return s
                elif True:
                    in11_ = default__.Tail(s)
                    in12_ = (n) - (1)
                    s = in11_
                    n = in12_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Drop(n, s):
        while True:
            with _dafny.label():
                if (n) == (0):
                    return s
                elif True:
                    in13_ = (n) - (1)
                    in14_ = default__.Tail(s)
                    n = in13_
                    s = in14_
                    raise _dafny.TailCall()
                break

