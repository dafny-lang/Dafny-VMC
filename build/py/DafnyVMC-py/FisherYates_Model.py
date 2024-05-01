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

# Module: FisherYates_Model

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Swap(s, i, j):
        if (i) == (j):
            return s
        elif True:
            d_39_t_ = ((((_dafny.SeqWithoutIsStrInference((s)[:i:])) + (_dafny.SeqWithoutIsStrInference([(s)[j]]))) + (_dafny.SeqWithoutIsStrInference((s)[(i) + (1):j:]))) + (_dafny.SeqWithoutIsStrInference([(s)[i]]))) + (_dafny.SeqWithoutIsStrInference((s)[(j) + (1)::]))
            return d_39_t_

