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

# Module: Uniform_Interface


class Trait:
    pass
    def UniformSample(self, n):
        pass

    @staticmethod
    def UniformIntervalSample(self, a, b):
        pass

    @staticmethod
    def UniformIntervalSample(self, a, b):
        u: int = int(0)
        d_37_v_: int
        out0_: int
        out0_ = (self).UniformSample((b) - (a))
        d_37_v_ = out0_
        u = (a) + (d_37_v_)
        return u


class Trait32:
    pass
    def UniformSample32(self, n):
        pass

    @staticmethod
    def UniformIntervalSample32(self, a, b):
        pass

    @staticmethod
    def UniformIntervalSample32(self, a, b):
        u: int = int(0)
        d_38_v_: int
        out1_: int
        out1_ = (self).UniformSample32((b) - (a))
        d_38_v_ = out1_
        u = (a) + (d_38_v_)
        return u

