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

# Module: Sequences

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def OneOverNPlus1(n):
        return (_dafny.BigRational('1e0')) / ((_dafny.BigRational(n, 1)) + (_dafny.BigRational('1e0')))

    @staticmethod
    def Suffix(sequence, offset):
        def lambda0_(d_5_sequence_, d_6_offset_):
            def lambda1_(d_7_n_):
                return d_5_sequence_((d_7_n_) + (d_6_offset_))

            return lambda1_

        return lambda0_(sequence, offset)

    @staticmethod
    def Constant(constant):
        def lambda2_(d_8_constant_):
            def lambda3_(d_9___v0_):
                return d_8_constant_

            return lambda3_

        return lambda2_(constant)

    @staticmethod
    def Add(sequence1, sequence2):
        def lambda4_(d_10_sequence1_, d_11_sequence2_):
            def lambda5_(d_12_n_):
                return (d_10_sequence1_(d_12_n_)) + (d_11_sequence2_(d_12_n_))

            return lambda5_

        return lambda4_(sequence1, sequence2)

    @staticmethod
    def Mul(sequence1, sequence2):
        def lambda6_(d_13_sequence1_, d_14_sequence2_):
            def lambda7_(d_15_n_):
                return (d_13_sequence1_(d_15_n_)) * (d_14_sequence2_(d_15_n_))

            return lambda7_

        return lambda6_(sequence1, sequence2)

    @staticmethod
    def Inverse(sequence):
        def lambda8_(d_16_sequence_):
            def lambda9_(d_17_n_):
                return (_dafny.BigRational('1e0')) / (d_16_sequence_(d_17_n_))

            return lambda9_

        return lambda8_(sequence)

