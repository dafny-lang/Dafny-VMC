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

# Module: FisherYates_Interface


class Trait:
    pass
    def Shuffle(self, a):
        pass

