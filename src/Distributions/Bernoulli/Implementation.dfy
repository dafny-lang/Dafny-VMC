/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Rationals.dfy"
include "Interface.dfy"
include "Model.dfy"

module BernoulliImplementation {
  import Rationals
  import Model = BernoulliModel
  import Interface = BernoulliInterface

  trait {:termination false} Trait extends Interface.Trait {

    method BernoulliSample(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures Model.ProbBernoulli(p.numer, p.denom)(old(s)) == (c, s)
    {
      var k := UniformSample(p.denom);
      c := k < p.numer;
    }

  }
}
