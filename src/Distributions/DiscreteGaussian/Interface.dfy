/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../BernoulliExpNeg/Interface.dfy"
include "../DiscreteLaplace/Interface.dfy"

module DiscreteGaussianInterface {
  import BernoulliExpNegInterface
  import DiscreteLaplaceInterface

  trait {:termination false} IDiscreteGaussian extends DiscreteLaplaceInterface.IDiscreteLaplace, BernoulliExpNegInterface.IBernoulliExpNeg {
    method DiscreteGaussian(sigma: real) returns (y: int)
      modifies this
      requires sigma > 0.0
      decreases *
  }
}
