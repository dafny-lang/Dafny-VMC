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

# Module: DafnyVMCTrait


class RandomTrait:
    pass
    @staticmethod
    def UniformSample(self, n):
        o: int = int(0)
        d_42_x_: int
        out3_: int
        out3_ = (self).UniformPowerOfTwoSample((2) * (n))
        d_42_x_ = out3_
        while not((d_42_x_) < (n)):
            out4_: int
            out4_ = (self).UniformPowerOfTwoSample((2) * (n))
            d_42_x_ = out4_
        d_43_r_: int
        d_43_r_ = d_42_x_
        o = d_43_r_
        return o

    @staticmethod
    def BernoulliSample(self, num, den):
        pass

    @staticmethod
    def BernoulliSample(self, num, den):
        o: bool = False
        d_44_d_: int
        out5_: int
        out5_ = (self).UniformSample(den)
        d_44_d_ = out5_
        o = (d_44_d_) < (num)
        return o

    @staticmethod
    def BernoulliExpNegSampleUnitLoop(self, num, den, state):
        pass

    @staticmethod
    def BernoulliExpNegSampleUnitLoop(self, num, den, state):
        o: tuple = (False, Pos.pos.default())
        d_45_A_: bool
        out6_: bool
        out6_ = (self).BernoulliSample(num, ((state)[1]) * (den))
        d_45_A_ = out6_
        o = (d_45_A_, ((state)[1]) + (1))
        return o

    @staticmethod
    def BernoulliExpNegSampleUnitAux(self, num, den):
        pass

    @staticmethod
    def BernoulliExpNegSampleUnitAux(self, num, den):
        o: int = int(0)
        d_46_state_: tuple
        d_46_state_ = (True, 1)
        while (d_46_state_)[0]:
            out7_: tuple
            out7_ = (self).BernoulliExpNegSampleUnitLoop(num, den, d_46_state_)
            d_46_state_ = out7_
        d_47_r_: tuple
        d_47_r_ = d_46_state_
        o = (d_47_r_)[1]
        return o

    @staticmethod
    def BernoulliExpNegSampleUnit(self, num, den):
        pass

    @staticmethod
    def BernoulliExpNegSampleUnit(self, num, den):
        o: bool = False
        d_48_K_: int
        out8_: int
        out8_ = (self).BernoulliExpNegSampleUnitAux(num, den)
        d_48_K_ = out8_
        if (_dafny.euclidian_modulus(d_48_K_, 2)) == (0):
            o = True
        elif True:
            o = False
        return o

    @staticmethod
    def BernoulliExpNegSampleGenLoop(self, iter):
        pass

    @staticmethod
    def BernoulliExpNegSampleGenLoop(self, iter):
        o: bool = False
        if (iter) == (0):
            o = True
        elif True:
            d_49_B_: bool
            out9_: bool
            out9_ = (self).BernoulliExpNegSampleUnit(1, 1)
            d_49_B_ = out9_
            if not((d_49_B_) == (True)):
                o = d_49_B_
            elif True:
                d_50_R_: bool
                out10_: bool
                out10_ = (self).BernoulliExpNegSampleGenLoop((iter) - (1))
                d_50_R_ = out10_
                o = d_50_R_
        return o

    @staticmethod
    def BernoulliExpNegSample(self, num, den):
        pass

    @staticmethod
    def BernoulliExpNegSample(self, num, den):
        o: bool = False
        if (num) <= (den):
            d_51_X_: bool
            out11_: bool
            out11_ = (self).BernoulliExpNegSampleUnit(num, den)
            d_51_X_ = out11_
            o = d_51_X_
        elif True:
            d_52_gamf_: int
            d_52_gamf_ = _dafny.euclidian_division(num, den)
            d_53_B_: bool
            out12_: bool
            out12_ = (self).BernoulliExpNegSampleGenLoop(d_52_gamf_)
            d_53_B_ = out12_
            if (d_53_B_) == (True):
                d_54_X_: bool
                out13_: bool
                out13_ = (self).BernoulliExpNegSampleUnit(_dafny.euclidian_modulus(num, den), den)
                d_54_X_ = out13_
                o = d_54_X_
            elif True:
                o = False
        return o

    @staticmethod
    def DiscreteLaplaceSampleLoopIn1Aux(self, t):
        pass

    @staticmethod
    def DiscreteLaplaceSampleLoopIn1Aux(self, t):
        o: tuple = (int(0), False)
        d_55_U_: int
        out14_: int
        out14_ = (self).UniformSample(t)
        d_55_U_ = out14_
        d_56_D_: bool
        out15_: bool
        out15_ = (self).BernoulliExpNegSample(d_55_U_, t)
        d_56_D_ = out15_
        o = (d_55_U_, d_56_D_)
        return o

    @staticmethod
    def DiscreteLaplaceSampleLoopIn1(self, t):
        pass

    @staticmethod
    def DiscreteLaplaceSampleLoopIn1(self, t):
        o: int = int(0)
        d_57_x_: tuple
        out16_: tuple
        out16_ = (self).DiscreteLaplaceSampleLoopIn1Aux(t)
        d_57_x_ = out16_
        while not((d_57_x_)[1]):
            out17_: tuple
            out17_ = (self).DiscreteLaplaceSampleLoopIn1Aux(t)
            d_57_x_ = out17_
        d_58_r1_: tuple
        d_58_r1_ = d_57_x_
        o = (d_58_r1_)[0]
        return o

    @staticmethod
    def DiscreteLaplaceSampleLoopIn2Aux(self, num, den, K):
        pass

    @staticmethod
    def DiscreteLaplaceSampleLoopIn2Aux(self, num, den, K):
        o: tuple = (False, int(0))
        d_59_A_: bool
        out18_: bool
        out18_ = (self).BernoulliExpNegSample(num, den)
        d_59_A_ = out18_
        o = (d_59_A_, ((K)[1]) + (1))
        return o

    @staticmethod
    def DiscreteLaplaceSampleLoopIn2(self, num, den):
        pass

    @staticmethod
    def DiscreteLaplaceSampleLoopIn2(self, num, den):
        o: int = int(0)
        d_60_K_: tuple
        d_60_K_ = (True, 0)
        while (d_60_K_)[0]:
            out19_: tuple
            out19_ = (self).DiscreteLaplaceSampleLoopIn2Aux(num, den, d_60_K_)
            d_60_K_ = out19_
        d_61_r2_: tuple
        d_61_r2_ = d_60_K_
        o = (d_61_r2_)[1]
        return o

    @staticmethod
    def DiscreteLaplaceSampleLoop(self, num, den):
        pass

    @staticmethod
    def DiscreteLaplaceSampleLoop(self, num, den):
        o: tuple = (False, int(0))
        d_62_v_: int
        out20_: int
        out20_ = (self).DiscreteLaplaceSampleLoopIn2(den, num)
        d_62_v_ = out20_
        d_63_V_: int
        d_63_V_ = (d_62_v_) - (1)
        d_64_B_: bool
        out21_: bool
        out21_ = (self).BernoulliSample(1, 2)
        d_64_B_ = out21_
        o = (d_64_B_, d_63_V_)
        return o

    @staticmethod
    def DiscreteLaplaceSample(self, num, den):
        pass

    @staticmethod
    def DiscreteLaplaceSample(self, num, den):
        o: int = int(0)
        d_65_x_: tuple
        out22_: tuple
        out22_ = (self).DiscreteLaplaceSampleLoop(num, den)
        d_65_x_ = out22_
        while not(not((((d_65_x_)[0]) == (True)) and (((d_65_x_)[1]) == (0)))):
            out23_: tuple
            out23_ = (self).DiscreteLaplaceSampleLoop(num, den)
            d_65_x_ = out23_
        d_66_r_: tuple
        d_66_r_ = d_65_x_
        d_67_Z_: int
        d_67_Z_ = ((0) - ((d_66_r_)[1]) if ((d_66_r_)[0]) == (True) else (d_66_r_)[1])
        o = d_67_Z_
        return o

    @staticmethod
    def DiscreteGaussianSampleLoop(self, num, den, t):
        pass

    @staticmethod
    def DiscreteGaussianSampleLoop(self, num, den, t):
        o: tuple = (int(0), False)
        d_68_Y_: int
        out24_: int
        out24_ = (self).DiscreteLaplaceSample(t, 1)
        d_68_Y_ = out24_
        d_69_y_: int
        d_69_y_ = ((0) - (d_68_Y_) if (d_68_Y_) < (0) else d_68_Y_)
        d_70_n_: int
        d_70_n_ = ((((((0) - (d_69_y_)) * (t)) * (den)) - (num) if ((((d_69_y_) * (t)) * (den)) - (num)) < (0) else (((d_69_y_) * (t)) * (den)) - (num))) * ((((((0) - (d_69_y_)) * (t)) * (den)) - (num) if ((((d_69_y_) * (t)) * (den)) - (num)) < (0) else (((d_69_y_) * (t)) * (den)) - (num)))
        d_71_d_: int
        d_71_d_ = ((((2) * (num)) * (t)) * (t)) * (den)
        d_72_C_: bool
        out25_: bool
        out25_ = (self).BernoulliExpNegSample(d_70_n_, d_71_d_)
        d_72_C_ = out25_
        o = (d_68_Y_, d_72_C_)
        return o

    @staticmethod
    def DiscreteGaussianSample(self, num, den):
        pass

    @staticmethod
    def DiscreteGaussianSample(self, num, den):
        o: int = int(0)
        d_73_ti_: int
        d_73_ti_ = _dafny.euclidian_division(num, den)
        d_74_t_: int
        d_74_t_ = (d_73_ti_) + (1)
        d_75_num_: int
        d_75_num_ = (num) * (num)
        d_76_den_: int
        d_76_den_ = (den) * (den)
        d_77_x_: tuple
        out26_: tuple
        out26_ = (self).DiscreteGaussianSampleLoop(d_75_num_, d_76_den_, d_74_t_)
        d_77_x_ = out26_
        while not((d_77_x_)[1]):
            out27_: tuple
            out27_ = (self).DiscreteGaussianSampleLoop(d_75_num_, d_76_den_, d_74_t_)
            d_77_x_ = out27_
        d_78_r_: tuple
        d_78_r_ = d_77_x_
        o = (d_78_r_)[0]
        return o

