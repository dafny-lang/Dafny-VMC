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
  import Loops

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
          var v := DisceteLaplaceInnerLoop();
          var x := u + scale.numer * v;
          y := x / scale.denom;
          b := CoinSample();
        }
      }
      z := if b then -y else y;
      assume {:axiom} false; // fix later
    }

    method DisceteLaplaceInnerLoop() returns (v: int)
      modifies this
      decreases *
      ensures Monad.Result(v, s) == Model.SampleInnerLoopFull()(old(s))
    {
      var a := true;
      v := 0;

      while a
        decreases *
        invariant Equivalence.SampleInnerLoopTailRecursive()(old(s)) == Equivalence.SampleInnerLoopTailRecursive((a, v))(s)
      {
        reveal Equivalence.SampleInnerLoopTailRecursive(); 
        
        a := BernoulliExpNegSample(Rationals.Int(1));
        if a {
          v := v + 1;
        }
      }

      Equivalence.SampleInnerLoopLiftToEnsures(old(s), s, a, v);
    }
  }
}
