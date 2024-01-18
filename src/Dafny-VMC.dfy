/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module {:extern "DafnyVMCMinus"} DafnyVMC {
  import Coin
  import Bernoulli
  import UniformPowerOfTwo
  import Uniform
  import BernoulliExpNeg
  import DiscreteGaussian
  import DiscreteLaplace
  import FisherYates

  trait Random extends Coin.Implementation.Trait, UniformPowerOfTwo.Implementation.Trait, Bernoulli.Implementation.Trait, Uniform.Implementation.Trait, BernoulliExpNeg.Implementation.Trait, DiscreteGaussian.Implementation.Trait, DiscreteLaplace.Implementation.Trait, FisherYates.Implementation.Trait  {
  }

}