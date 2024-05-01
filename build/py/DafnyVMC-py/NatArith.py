import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Pos
import DafnyVMCPartMaterial

# Module: NatArith

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Max(a, b):
        if (a) < (b):
            return b
        elif True:
            return a

    @staticmethod
    def Min(a, b):
        if (a) < (b):
            return a
        elif True:
            return b

    @staticmethod
    def Power(b, n):
        d_0___accumulator_ = 1
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (1) * (d_0___accumulator_)
                elif (n) == (1):
                    return (b) * (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = (d_0___accumulator_) * (b)
                    in0_ = b
                    in1_ = (n) - (1)
                    b = in0_
                    n = in1_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def Log2Floor(n):
        d_1___accumulator_ = 0
        while True:
            with _dafny.label():
                if (n) < (2):
                    return (0) + (d_1___accumulator_)
                elif True:
                    d_1___accumulator_ = (1) + (d_1___accumulator_)
                    in2_ = _dafny.euclidian_division(n, 2)
                    n = in2_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def boolToNat(b):
        if b:
            return 1
        elif True:
            return 0

    @staticmethod
    def Factorial(n, start):
        d_2___accumulator_ = 1
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (1) * (d_2___accumulator_)
                elif True:
                    d_2___accumulator_ = (d_2___accumulator_) * (start)
                    in3_ = (n) - (1)
                    in4_ = (start) + (1)
                    n = in3_
                    start = in4_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def FactorialTraditional(n):
        d_3___accumulator_ = 1
        while True:
            with _dafny.label():
                if (n) == (0):
                    return (1) * (d_3___accumulator_)
                elif True:
                    d_3___accumulator_ = (d_3___accumulator_) * (n)
                    in5_ = (n) - (1)
                    n = in5_
                    raise _dafny.TailCall()
                break

