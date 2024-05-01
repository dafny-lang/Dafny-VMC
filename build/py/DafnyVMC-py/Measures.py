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

# Module: Measures

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def AreIndepEvents(eventSpace, Prob, e1, e2):
        return (((e1) in (eventSpace)) and ((e2) in (eventSpace))) and ((Prob((e1).intersection(e2))) == ((Prob(e1)) * (Prob(e2))))


class Probability:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return _dafny.BigRational()
