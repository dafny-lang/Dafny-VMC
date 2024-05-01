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

# Module: Monad

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Bind(f, g):
        def lambda14_(d_23_f_, d_24_g_):
            def lambda15_(d_25_s_):
                return (d_23_f_(d_25_s_)).Bind(d_24_g_)

            return lambda15_

        return lambda14_(f, g)

    @staticmethod
    def Composition(f, g):
        def lambda16_(d_26_f_, d_27_g_):
            def lambda17_(d_28_a_):
                return default__.Bind(d_26_f_(d_28_a_), d_27_g_)

            return lambda17_

        return lambda16_(f, g)

    @staticmethod
    def Return(a):
        def lambda18_(d_29_a_):
            def lambda19_(d_30_s_):
                return Result_Result(d_29_a_, d_30_s_)

            return lambda19_

        return lambda18_(a)

    @staticmethod
    def Map(m, f):
        def lambda20_(d_31_f_):
            def lambda21_(d_32_a_):
                return default__.Return(d_31_f_(d_32_a_))

            return lambda21_

        return default__.Bind(m, lambda20_(f))

    @staticmethod
    def Join(ff):
        def lambda22_(d_33_ff_):
            def lambda23_(d_34_s_):
                def lambda24_(d_35_f_):
                    return d_35_f_

                return (d_33_ff_(d_34_s_)).Bind(lambda24_)

            return lambda23_

        return lambda22_(ff)

    @_dafny.classproperty
    def Coin(instance):
        def lambda25_(d_36_s_):
            return Result_Result(Rand.default__.Head(d_36_s_), Rand.default__.Tail(d_36_s_))

        return lambda25_

class Result:
    @classmethod
    def default(cls, default_A):
        return lambda: Result_Result(default_A(), (lambda x0: False))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Result(self) -> bool:
        return isinstance(self, Result_Result)
    def Map(self, f):
        return Result_Result(f((self).value), (self).rest)

    def Bind(self, f):
        return f((self).value)((self).rest)

    def Satisfies(self, property):
        return property((self).value)

    def RestSatisfies(self, property):
        return property((self).rest)

    def Extract(self):
        return ((self).value, (self).rest)


class Result_Result(Result, NamedTuple('Result', [('value', Any), ('rest', Any)])):
    def __dafnystr__(self) -> str:
        return f'Monad.Result.Result({_dafny.string_of(self.value)}, {_dafny.string_of(self.rest)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Result_Result) and self.value == __o.value and self.rest == __o.rest
    def __hash__(self) -> int:
        return super().__hash__()

