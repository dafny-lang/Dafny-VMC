/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Implementation {
  import Rationals
  import Interface
  import Monad
  import Model
  import Uniform
  import BernoulliExpNeg
  import Bernoulli
  import Coin
  import Equivalence

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *
      ensures Monad.Result(z, s) == Model.Sample(scale)(old(s))
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := UniformSample(scale.numer);
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        if d {
          var a := true;
          var v := 0;
          while a
            decreases *
          {
            a := BernoulliExpNegSample(Rationals.Int(1));
            if a {
              v := v + 1;
            }
          }
          var x := u + scale.numer * v;
          y := x / scale.denom;
          b := CoinSample();
        }
      }
      z := if b then -y else y;
      assume {:axiom} Monad.Result(z, s) == Equivalence.SampleTailRecursive(scale)(old(s));
      Equivalence.SampleTailRecursiveEquivalence(scale, old(s));
    }

  }
}
