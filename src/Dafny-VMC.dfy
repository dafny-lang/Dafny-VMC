/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Base/Interface.dfy"
include "Distributions/Bernoulli/Bernoulli.dfy"
include "Distributions/BernoulliExpNeg/Implementation.dfy"
include "Distributions/DiscreteGaussian/Implementation.dfy"
include "Distributions/DiscreteLaplace/Implementation.dfy"
include "Distributions/UniformPowerOfTwo/Implementation.dfy"
include "Distributions/Uniform/Implementation.dfy"

module DafnyVMC {
  import BaseInterface
  import Bernoulli
  import UniformPowerOfTwoImplementation
  import UniformImplementation
  import BernoulliExpNegImplementation
  import DiscreteGaussianImplementation
  import DiscreteLaplaceImplementation

  class DRandomFoundational extends BaseInterface.TBase, UniformPowerOfTwoImplementation.TUniformPowerOfTwo, Bernoulli.Implementation.TBernoulli, UniformImplementation.TUniformFoundational, BernoulliExpNegImplementation.TBernoulliExpNeg, DiscreteGaussianImplementation.TDiscreteGaussian, DiscreteLaplaceImplementation.TDiscreteLaplace {
    constructor {:extern} ()
  }

  class DRandomExternUniform extends BaseInterface.TBase, UniformPowerOfTwoImplementation.TUniformPowerOfTwo, Bernoulli.Implementation.TBernoulli, UniformImplementation.TUniformExtern, BernoulliExpNegImplementation.TBernoulliExpNeg, DiscreteGaussianImplementation.TDiscreteGaussian, DiscreteLaplaceImplementation.TDiscreteLaplace {
    constructor {:extern} ()
  }
}
