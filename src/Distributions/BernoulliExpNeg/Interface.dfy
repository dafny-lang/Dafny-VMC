/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "../../Math/Rationals.dfy"
include "../BernoulliRational/Interface.dfy"

module BernoulliExpNegInterface {
  import Rationals
  import BernoulliRationalInterface

  trait {:termination false} IBernoulliExpNeg extends BernoulliRationalInterface.IBernoulliRational {

    method BernoulliExpNeg(gamma: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires gamma.numer >= 0

  }
}
