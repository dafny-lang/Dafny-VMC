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
import FisherYates_Implementation
import FisherYates
import DafnyVMCTrait
import DafnyVMCPart

# Module: Helper

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def NatToString(n):
        if (n) == (0):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "0"))
        elif (n) == (1):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "1"))
        elif (n) == (2):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "2"))
        elif (n) == (3):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "3"))
        elif (n) == (4):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "4"))
        elif (n) == (5):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "5"))
        elif (n) == (6):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "6"))
        elif (n) == (7):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "7"))
        elif (n) == (8):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "8"))
        elif (n) == (9):
            return _dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "9"))
        elif True:
            return (default__.NatToString(_dafny.euclidian_division(n, 10))) + (default__.NatToString(_dafny.euclidian_modulus(n, 10)))

    @staticmethod
    def SeqToString(xs, printer):
        d_79___accumulator_ = _dafny.SeqWithoutIsStrInference([])
        while True:
            with _dafny.label():
                if (len(xs)) == (0):
                    return (d_79___accumulator_) + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "")))
                elif True:
                    d_79___accumulator_ = (d_79___accumulator_) + (printer((xs)[0]))
                    in15_ = _dafny.SeqWithoutIsStrInference((xs)[1::])
                    in16_ = printer
                    xs = in15_
                    printer = in16_
                    raise _dafny.TailCall()
                break

