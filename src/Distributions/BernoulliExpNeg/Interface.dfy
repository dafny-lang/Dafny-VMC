/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../../Math/Rationals.dfy"
include "../Bernoulli/Interface.dfy"

module BernoulliExpNegInterface {
  import Rationals
  import BernoulliInterface

  trait {:termination false} IBernoulliExpNeg extends BernoulliInterface.IBernoulli {

    method BernoulliExpNeg(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires gamma.numer >= 0

  }
}
