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
import Helper

# Module: Rationals

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Int(n):
        return Rational_Rational(n, 1)


class PosInt:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return 1

class Rational:
    @classmethod
    def default(cls, ):
        return lambda: Rational_Rational(int(0), PosInt.default())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Rational(self) -> bool:
        return isinstance(self, Rational_Rational)
    def Eq(self, rhs):
        return (((self).numer) * ((rhs).denom)) == (((rhs).numer) * ((self).denom))

    def Leq(self, rhs):
        return (((self).numer) * ((rhs).denom)) <= (((rhs).numer) * ((self).denom))

    def Neg(self):
        return Rational_Rational((0) - ((self).numer), (self).denom)

    def Add(self, rhs):
        return Rational_Rational((((self).numer) * ((rhs).denom)) + (((rhs).numer) * ((self).denom)), ((self).denom) * ((rhs).denom))

    def Sub(self, rhs):
        return (self).Add((rhs).Neg())

    def Inv(self):
        d_80_denom_ = (self).denom
        if ((self).numer) < (0):
            return Rational_Rational((0) - (d_80_denom_), (0) - ((self).numer))
        elif True:
            return Rational_Rational(d_80_denom_, (self).numer)

    def Mul(self, rhs):
        return Rational_Rational(((self).numer) * ((rhs).numer), ((self).denom) * ((rhs).denom))

    def Div(self, rhs):
        return (self).Mul((rhs).Inv())

    def Floor(self):
        return _dafny.euclidian_division((self).numer, (self).denom)

    def FractionalPart(self):
        return Rational_Rational(_dafny.euclidian_modulus((self).numer, (self).denom), (self).denom)

    def ToReal(self):
        return (_dafny.BigRational((self).numer, 1)) / (_dafny.BigRational((self).denom, 1))


class Rational_Rational(Rational, NamedTuple('Rational', [('numer', Any), ('denom', Any)])):
    def __dafnystr__(self) -> str:
        return f'Rationals.Rational.Rational({_dafny.string_of(self.numer)}, {_dafny.string_of(self.denom)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Rational_Rational) and self.numer == __o.numer and self.denom == __o.denom
    def __hash__(self) -> int:
        return super().__hash__()

