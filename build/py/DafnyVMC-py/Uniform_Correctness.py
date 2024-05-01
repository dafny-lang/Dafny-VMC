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

# Module: Uniform_Correctness

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def IntervalSampleIsIndepFunctionHelper(a, x):
        return (x) - (a)

