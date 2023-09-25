/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Base/Interface.dfy"
include "Distributions/Bernoulli/Implementation.dfy"
include "Distributions/BernoulliExpNeg/Implementation.dfy"
include "Distributions/DiscreteGaussian/Implementation.dfy"
include "Distributions/DiscreteLaplace/Implementation.dfy"
include "Distributions/Geometric/Implementation.dfy"
include "Distributions/Uniform/Implementation.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened Base
  import opened Bernoulli
  import opened Geometric
  import opened Uniform
  import opened BernoulliExpNeg
  import opened DiscreteGaussian
  import opened DiscreteLaplace

  class {:extern} DRandomFoundational extends Base, Unif, Bernoulli, Geometric, UniformFoundational, BernoulliExpNeg, DiscreteGaussian, DiscreteLaplace {
    constructor {:extern} ()
  }

  class {:extern} DRandomExternUniform extends Base, Unif, Bernoulli, Geometric, UniformExtern, BernoulliExpNeg, DiscreteGaussian, DiscreteLaplace {
    constructor {:extern} ()
  }
}
