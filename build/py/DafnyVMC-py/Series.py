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

# Module: Series

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def SumFromTo(sequence, start, end):
        d_18___accumulator_ = _dafny.BigRational('0e0')
        while True:
            with _dafny.label():
                if (end) <= (start):
                    return (_dafny.BigRational('0e0')) + (d_18___accumulator_)
                elif True:
                    d_18___accumulator_ = (d_18___accumulator_) + (sequence(start))
                    in8_ = sequence
                    in9_ = (start) + (1)
                    in10_ = end
                    sequence = in8_
                    start = in9_
                    end = in10_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def SumTo(sequence, end):
        return default__.SumFromTo(sequence, 0, end)

    @staticmethod
    def PartialSums(sequence):
        def lambda10_(d_19_sequence_):
            def lambda11_(d_20_n_):
                return default__.SumTo(d_19_sequence_, d_20_n_)

            return lambda11_

        return lambda10_(sequence)

