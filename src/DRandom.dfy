/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Distributions/Base/Interface.dfy"
include "Distributions/Bernoulli/Interface.dfy"
include "Distributions/BernoulliExp/Interface.dfy"
include "Distributions/DiscreteGaussian/Interface.dfy"
include "Distributions/DiscreteLaplace/Interface.dfy"
include "Distributions/Geometric/Interface.dfy"
include "Distributions/Uniform/Interface.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {

  class {:extern} DRandomFoundational extends Base, Unif, Bernoulli__, UniformFoundational, BernoulliExpNeg, DiscreteGaussian, DiscreteLaplace {
    constructor {:extern} ()
  }

  class {:extern} DRandomExternUniform extends Base, Unif, Bernoulli__, UniformExtern, BernoulliExpNeg, DiscreteGaussian, DiscreteLaplace {
    constructor {:extern} ()
  }

}
