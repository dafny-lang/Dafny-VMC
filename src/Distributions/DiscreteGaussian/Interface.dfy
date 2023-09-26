/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../BernoulliExpNeg/Interface.dfy"
include "../DiscreteLaplace/Interface.dfy"

module DiscreteGaussianInterface {
  import opened BernoulliExpNegInterface
  import opened DiscreteLaplaceInterface

  trait {:termination false} IDiscreteGaussian extends IDiscreteLaplace, IBernoulliExpNeg {
    method DiscreteGaussian(sigma: real) returns (y: int)
      modifies this
      requires sigma > 0.0
      decreases *
  }
}
