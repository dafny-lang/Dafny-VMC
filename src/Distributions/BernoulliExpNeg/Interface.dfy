/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Bernoulli/Interface.dfy"

module BernoulliExpNegInterface {
  import BernoulliInterface

  trait {:termination false} IBernoulliExpNeg extends BernoulliInterface.IBernoulli {

    method BernoulliExpNeg(gamma: real) returns (c: bool)
      modifies this
      decreases *
      requires gamma >= 0.0

  }
}
