/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../BernoulliExpNeg/Interface.dfy"
include "../DiscreteLaplace/Interface.dfy"

module DiscreteGaussianInterface {
  import Rationals
  import BernoulliExpNegInterface
  import DiscreteLaplaceInterface

  trait {:termination false} IDiscreteGaussian extends DiscreteLaplaceInterface.IDiscreteLaplace, BernoulliExpNegInterface.IBernoulliExpNeg {
    // Takes the sigma (not sigma^2!) as a fraction
    method DiscreteGaussian(sigma: Rationals.Rational) returns (y: int)
      modifies this
      requires sigma.numer >= 1
      decreases *
  }
}
