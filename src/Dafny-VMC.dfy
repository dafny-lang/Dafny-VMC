/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

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

  class DRandomExternUniform extends Coin.Interface.Trait, UniformPowerOfTwo.Implementation.TraitExtern, Bernoulli.Implementation.Trait, Uniform.Implementation.TraitFoundational, BernoulliExpNeg.Implementation.Trait, DiscreteGaussian.Implementation.Trait, DiscreteLaplace.Implementation.Trait {
    constructor {:extern} ()
  }
}
