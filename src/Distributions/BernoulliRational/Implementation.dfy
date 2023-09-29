/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"
include "Model.dfy"

module BernoulliRationalImplementation {
  import Rationals
  import BernoulliRationalModel
  import BernoulliRationalInterface

  trait {:termination false} TBernoulliRational extends BernoulliRationalInterface.IBernoulliRational {

    method BernoulliRational(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures BernoulliRationalModel.ProbBernoulliRational(p.numer, p.denom)(old(s)) == (c, s)
    {
      var k := Uniform(p.denom);
      c := k < p.numer;
    }

  }
}
