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
      ensures Model.Sample(scale)(old(s)) == Monad.Result(z, s)
    {
      var x := DiscreteLaplaceSampleLoop(scale);
      Equivalence.SampleLiftToEnsures(scale, s, old(s), x);
      z := if x.0 then -x.1 else x.1;
    }

    method {:rlimit 100000} DiscreteLaplaceSampleLoop(scale: Rationals.Rational) returns (bY: (bool, int))
      modifies this
      requires scale.numer >= 1
      decreases *
      ensures Model.SampleLoop(scale)(old(s)) == Monad.Result(bY, s)
    {
      var b := true;
      var y := 0;


      while b && y == 0
        decreases *
        invariant Model.SampleLoop(scale)(old(s)) == Model.SampleLoop(scale, (b, y))(s)
      {
        Equivalence.SampleLoopTailRecursiveEquivalence(scale, s, (b, y));

        var u := UniformSample(scale.numer);
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        if d {
          var v := DisceteLaplaceSampleInnerLoop();
          b := CoinSample();
          var x := u + scale.numer * v;
          y := x / scale.denom;
        }
      }

      Equivalence.SampleLoopLiftToEnsures(scale, old(s), s, (b, y));

      return (b, y);
    }

    method DisceteLaplaceSampleInnerLoop() returns (v: int)
      modifies this
      decreases *
      ensures Model.SampleInnerLoopFull()(old(s)) == Monad.Result(v, s)
    {
      var a := true;
      v := 0;

      while a
        decreases *
        invariant Model.SampleInnerLoop()(old(s)) == Model.SampleInnerLoop((a, v))(s)
      {
        Equivalence.SampleInnerLoopTailRecursiveEquivalence(s, (a, v));

        a := BernoulliExpNegSample(Rationals.Int(1));
        if a {
          v := v + 1;
        }
      }

      Equivalence.SampleInnerLoopLiftToEnsures(old(s), s, a, v);
    }
  }
}
