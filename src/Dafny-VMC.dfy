/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Base/Interface.dfy"
include "Distributions/Bernoulli/Implementation.dfy"
include "Distributions/BernoulliRational/Implementation.dfy"
include "Distributions/BernoulliExpNeg/Implementation.dfy"
include "Distributions/DiscreteGaussian/Implementation.dfy"
include "Distributions/DiscreteLaplace/Implementation.dfy"
include "Distributions/Geometric/Implementation.dfy"
include "Distributions/UniformPowerOfTwo/Implementation.dfy"
include "Distributions/Uniform/Implementation.dfy"

module DafnyVMC {
  import opened BaseInterface
  import opened BernoulliImplementation
  import opened BernoulliRationalImplementation
  import opened GeometricImplementation
  import opened UniformPowerOfTwoImplementation
  import opened UniformImplementation
  import opened BernoulliExpNegImplementation
  import opened DiscreteGaussianImplementation
  import opened DiscreteLaplaceImplementation

  class DRandomFoundational extends TBase, TUniformPowerOfTwo, TBernoulli, TBernoulliRational, TGeometric, TUniformFoundational, TBernoulliExpNeg, TDiscreteGaussian, TDiscreteLaplace {
    constructor {:extern} ()
  }

  class DRandomExternUniform extends TBase, TUniformPowerOfTwo, TBernoulli, TBernoulliRational, TGeometric, TUniformExtern, TBernoulliExpNeg, TDiscreteGaussian, TDiscreteLaplace {
    constructor {:extern} ()
  }
}
