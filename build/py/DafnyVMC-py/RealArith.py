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

# Module: RealArith

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Abs(r):
        if (r) >= (_dafny.BigRational('0e0')):
            return r
        elif True:
            return (_dafny.BigRational('0e0')) - (r)

    @staticmethod
    def Max(x, y):
        if (x) >= (y):
            return x
        elif True:
            return y

    @staticmethod
    def Min(x, y):
        if (x) <= (y):
            return x
        elif True:
            return y

    @staticmethod
    def Dist(x, y):
        return default__.Abs((x) - (y))

    @staticmethod
    def Pow(base, exponent):
        d_4___accumulator_ = _dafny.BigRational('1e0')
        while True:
            with _dafny.label():
                if (exponent) == (0):
                    return (_dafny.BigRational('1e0')) * (d_4___accumulator_)
                elif True:
                    d_4___accumulator_ = (d_4___accumulator_) * (base)
                    in6_ = base
                    in7_ = (exponent) - (1)
                    base = in6_
                    exponent = in7_
                    raise _dafny.TailCall()
                break

