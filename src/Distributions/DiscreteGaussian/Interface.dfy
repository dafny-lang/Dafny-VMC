/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../BernoulliExpNeg/BernoulliExpNeg.dfy"
include "../DiscreteLaplace/DiscreteLaplace.dfy"

module Interface {
  import Rationals
  import BernoulliExpNeg
  import DiscreteLaplace

  trait {:termination false} Trait extends DiscreteLaplace.Interface.Trait, BernoulliExpNeg.Interface.Trait {
    // Takes the sigma (not sigma^2!) as a fraction
    method DiscreteGaussianSample(sigma: Rationals.Rational) returns (y: int)
      modifies this
      requires sigma.numer >= 1
      decreases *
  }
}
