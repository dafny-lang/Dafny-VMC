/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Bernoulli/Interface.dfy"

module BernoulliExpNegInterface {
  import opened BernoulliInterface
  
  trait {:termination false} IBernoulliExpNeg extends IBernoulli {

    method BernoulliExpNeg(gamma: real) returns (c: bool)
      modifies this
      decreases *
      requires gamma >= 0.0

  }
}
