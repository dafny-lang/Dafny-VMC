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
          var v := DiscreteLaplaceSampleHelper();
          var x := u + scale.numer * v;
          y := x / scale.denom;
          b := CoinSample();
        }
      }
      z := if b then -y else y;
      assume {:axiom} Monad.Result(z, s) == Equivalence.SampleTailRecursive(scale)(old(s));
      Equivalence.SampleTailRecursiveEquivalence(scale, old(s));
    }

    method DiscreteLaplaceSampleHelper() returns (v: int)
      modifies this
      decreases *
      ensures Model.SampleHelper.requires(old(s))
      ensures Model.SampleHelper(old(s)) == Monad.Result(v, s)
    {
      assume {:axiom} Model.SampleHelper.requires(old(s));  // proof related
      ghost var fuel := Loops.LeastFuel(Model.SampleHelperLoopCondition, Model.SampleHelperLoopBody, (true, 0), old(s));  // proof related
      ghost var f := (x: (bool, int)) => x.1;  // proof related

      var a := true;
      v := 0;

      while a
        decreases *
        invariant Equivalence.SampleTailRecursiveHelperLoop(old(s)) == Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s)  // proof related
      {
        assume {:axiom} fuel > 0; // proof related
        fuel := fuel - 1; // proof related

        a := BernoulliExpNegSample(Rationals.Int(1));
        if a {
          v := v + 1;
        }
      }

      // proof related
      calc {
        Model.SampleHelper(old(s));
        { Equivalence.SampleTailRecursiveHelperEquivalence(old(s)); }
        Equivalence.SampleTailRecursiveHelper(old(s));
        Equivalence.SampleTailRecursiveHelperLoop(old(s)).Map(f);
        { assert Equivalence.SampleTailRecursiveHelperLoop(old(s)) == Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s); }
        Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s).Map(f);
        { assert Equivalence.SampleTailRecursiveHelperLoopCut((a, v), fuel)(s) == Monad.Result((a, v), s); }
        Monad.Result((a, v), s).Map(f);
        Monad.Result(v, s);
      }

    }
  }
}
