/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../BernoulliExpNeg/Interface.dfy"
include "../DiscreteLaplace/Interface.dfy"

trait IDiscreteGaussian extends IDiscreteLaplace, IBernoulliExpNeg {

  // Based on Algorithm 3 in https://arxiv.org/pdf/2004.00010.pdf; unverified
  // Note that we take sigma as a parameter, not sigma^2, to avoid square roots.
  method DiscreteGaussian(sigma: real) returns (y: int)
    modifies this
    requires sigma > 0.0
    decreases *

}
