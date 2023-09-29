/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"
include "Model.dfy"

module BernoulliImplementation {
  import Rationals
  import BernoulliModel
  import BernoulliInterface

  trait {:termination false} TBernoulli extends BernoulliInterface.IBernoulli {

    method Bernoulli(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures BernoulliModel.ProbBernoulli(p.numer, p.denom)(old(s)) == (c, s)
    {
      var k := Uniform(p.denom);
      c := k < p.numer;
    }

  }
}
