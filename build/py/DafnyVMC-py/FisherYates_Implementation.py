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
import Rand
import Bitstream_Interface
import Bitstream
import UniformPowerOfTwo_Interface
import UniformPowerOfTwo
import Monad
import Independence
import Uniform_Model
import Uniform_Correctness
import Uniform_Interface
import Uniform
import FisherYates_Model
import FisherYates_Correctness
import FisherYates_Equivalence
import FisherYates_Interface

# Module: FisherYates_Implementation


class Trait:
    pass
    @staticmethod
    def Shuffle(self, a):
        if ((a).length(0)) > (1):
            hi0_ = ((a).length(0)) - (1)
            for d_40_i_ in range(0, hi0_):
                d_41_j_: int
                out2_: int
                out2_ = (self).UniformIntervalSample32(d_40_i_, (a).length(0))
                d_41_j_ = out2_
                (self).Swap(a, d_40_i_, d_41_j_)
        elif True:
            pass

    @staticmethod
    def Swap(self, a, i, j):
        pass

    @staticmethod
    def Swap(self, a, i, j):
        rhs0_ = (a)[j]
        rhs1_ = (a)[i]
        lhs0_ = a
        lhs1_ = i
        lhs2_ = a
        lhs3_ = j
        lhs0_[lhs1_] = rhs0_
        lhs2_[lhs3_] = rhs1_

