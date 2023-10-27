/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Implementation {
  import Rationals
  import Monad`Bernoulli
  import Model
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    method BernoulliSample(p: Rationals.Rational) returns (c: bool)
      modifies this
      decreases *
      requires 0 <= p.numer <= p.denom
      ensures Model.Sample(p.numer, p.denom)(old(s)) == Monad.Result(c, s)
    {
      reveal Model.Sample();
      var k := UniformSample(p.denom);
      c := k < p.numer;
      reveal Model.Sample();
    }

  }
}
