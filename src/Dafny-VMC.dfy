/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Base/Interface.dfy"
include "Distributions/Bernoulli/Implementation.dfy"
include "Distributions/Bernoulli/Implementation.dfy"
include "Distributions/BernoulliExpNeg/Implementation.dfy"
include "Distributions/DiscreteGaussian/Implementation.dfy"
include "Distributions/DiscreteLaplace/Implementation.dfy"
include "Distributions/Geometric/Implementation.dfy"
include "Distributions/UniformPowerOfTwo/Implementation.dfy"
include "Distributions/Uniform/Implementation.dfy"

module DafnyVMC {
  import BaseInterface
  import BernoulliImplementation
  import GeometricImplementation
  import UniformPowerOfTwoImplementation
  import UniformImplementation
  import BernoulliExpNegImplementation
  import DiscreteGaussianImplementation
  import DiscreteLaplaceImplementation

  class DRandomFoundational extends BaseInterface.TBase, UniformPowerOfTwoImplementation.TUniformPowerOfTwo, BernoulliImplementation.TBernoulli, GeometricImplementation.TGeometric, UniformImplementation.TUniformFoundational, BernoulliExpNegImplementation.TBernoulliExpNeg, DiscreteGaussianImplementation.TDiscreteGaussian, DiscreteLaplaceImplementation.TDiscreteLaplace {
    constructor {:extern} ()
  }

  class DRandomExternUniform extends BaseInterface.TBase, UniformPowerOfTwoImplementation.TUniformPowerOfTwo, BernoulliImplementation.TBernoulli, GeometricImplementation.TGeometric, UniformImplementation.TUniformExtern, BernoulliExpNegImplementation.TBernoulliExpNeg, DiscreteGaussianImplementation.TDiscreteGaussian, DiscreteLaplaceImplementation.TDiscreteLaplace {
    constructor {:extern} ()
  }
}
