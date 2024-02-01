/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteGaussian.Interface {
  import Rationals
  import BernoulliExpNeg
  import DiscreteLaplace

  trait {:termination false} Trait extends DiscreteLaplace.Interface.Trait, BernoulliExpNeg.Interface.Trait {
    // Takes the sigma (not sigma^2!) as a fraction
    method DiscreteGaussianSample(sigma: Rationals.Rational) returns (y: int)
      modifies `s
      requires sigma.numer >= 1
      decreases *
  }
}
