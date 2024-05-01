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

# Module: DafnyVMCPart


class Random(DafnyVMCTrait.RandomTrait, UniformPowerOfTwo_Interface.Trait, FisherYates_Implementation.Trait, Uniform_Interface.Trait, Bitstream_Interface.Trait, FisherYates_Interface.Trait, Uniform_Interface.Trait32):
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "DafnyVMC.Random"
    def UniformSample(self, n):
        out28_: int
        out28_ = DafnyVMCTrait.RandomTrait.UniformSample(self, n)
        return out28_

    def BernoulliSample(self, num, den):
        out29_: bool
        out29_ = DafnyVMCTrait.RandomTrait.BernoulliSample(self, num, den)
        return out29_

    def BernoulliExpNegSampleUnitLoop(self, num, den, state):
        out30_: tuple
        out30_ = DafnyVMCTrait.RandomTrait.BernoulliExpNegSampleUnitLoop(self, num, den, state)
        return out30_

    def BernoulliExpNegSampleUnitAux(self, num, den):
        out31_: int
        out31_ = DafnyVMCTrait.RandomTrait.BernoulliExpNegSampleUnitAux(self, num, den)
        return out31_

    def BernoulliExpNegSampleUnit(self, num, den):
        out32_: bool
        out32_ = DafnyVMCTrait.RandomTrait.BernoulliExpNegSampleUnit(self, num, den)
        return out32_

    def BernoulliExpNegSampleGenLoop(self, iter):
        out33_: bool
        out33_ = DafnyVMCTrait.RandomTrait.BernoulliExpNegSampleGenLoop(self, iter)
        return out33_

    def BernoulliExpNegSample(self, num, den):
        out34_: bool
        out34_ = DafnyVMCTrait.RandomTrait.BernoulliExpNegSample(self, num, den)
        return out34_

    def DiscreteLaplaceSampleLoopIn1Aux(self, t):
        out35_: tuple
        out35_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSampleLoopIn1Aux(self, t)
        return out35_

    def DiscreteLaplaceSampleLoopIn1(self, t):
        out36_: int
        out36_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSampleLoopIn1(self, t)
        return out36_

    def DiscreteLaplaceSampleLoopIn2Aux(self, num, den, K):
        out37_: tuple
        out37_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSampleLoopIn2Aux(self, num, den, K)
        return out37_

    def DiscreteLaplaceSampleLoopIn2(self, num, den):
        out38_: int
        out38_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSampleLoopIn2(self, num, den)
        return out38_

    def DiscreteLaplaceSampleLoop(self, num, den):
        out39_: tuple
        out39_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSampleLoop(self, num, den)
        return out39_

    def DiscreteLaplaceSample(self, num, den):
        out40_: int
        out40_ = DafnyVMCTrait.RandomTrait.DiscreteLaplaceSample(self, num, den)
        return out40_

    def DiscreteGaussianSampleLoop(self, num, den, t):
        out41_: tuple
        out41_ = DafnyVMCTrait.RandomTrait.DiscreteGaussianSampleLoop(self, num, den, t)
        return out41_

    def DiscreteGaussianSample(self, num, den):
        out42_: int
        out42_ = DafnyVMCTrait.RandomTrait.DiscreteGaussianSample(self, num, den)
        return out42_

    def Shuffle(self, a):
        FisherYates_Implementation.Trait.Shuffle(self, a)
        return 

    def Swap(self, a, i, j):
        FisherYates_Implementation.Trait.Swap(self, a, i, j)
        return 

    def UniformIntervalSample32(self, a, b):
        out43_: int
        out43_ = Uniform_Interface.Trait32.UniformIntervalSample32(self, a, b)
        return out43_

    def UniformIntervalSample(self, a, b):
        out44_: int
        out44_ = Uniform_Interface.Trait.UniformIntervalSample(self, a, b)
        return out44_

    def UniformPowerOfTwoSample(self, n):
        u: int = int(0)
        out45_: int
        out45_ = DafnyVMCPartMaterial.Random.UniformPowerOfTwoSample(n)
        u = out45_
        return u

    def UniformSample32(self, n):
        u: int = Pos.nat32.default()
        out46_: int
        out46_ = DafnyVMCPartMaterial.Random.UniformSample32(n)
        u = out46_
        return u

