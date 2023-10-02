/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Coin/Coin.dfy"
include "Distributions/Bernoulli/Bernoulli.dfy"
include "Distributions/BernoulliExpNeg/BernoulliExpNeg.dfy"
include "Distributions/DiscreteGaussian/DiscreteGaussian.dfy"
include "Distributions/DiscreteLaplace/DiscreteLaplace.dfy"
include "Distributions/UniformPowerOfTwo/UniformPowerOfTwo.dfy"
include "Distributions/Uniform/Uniform.dfy"

module DafnyVMC {
  import Coin
  import Bernoulli
  import UniformPowerOfTwo
  import Uniform
  import BernoulliExpNeg
  import DiscreteGaussian
  import DiscreteLaplace

  class DRandomFoundational extends Coin.Interface.Trait, UniformPowerOfTwo.Implementation.Trait, Bernoulli.Implementation.Trait, Uniform.Implementation.TraitFoundational, BernoulliExpNeg.Implementation.Trait, DiscreteGaussian.Implementation.Trait, DiscreteLaplace.Implementation.Trait {
    constructor {:extern} ()
  }

  class DRandomExternUniform extends Coin.Interface.Trait, UniformPowerOfTwo.Implementation.Trait, Bernoulli.Implementation.Trait, Uniform.Implementation.TraitExtern, BernoulliExpNeg.Implementation.Trait, DiscreteGaussian.Implementation.Trait, DiscreteLaplace.Implementation.Trait {
    constructor {:extern} ()
  }
}
