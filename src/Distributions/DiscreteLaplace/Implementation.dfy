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
      // ghost var prevB := b;
      // ghost var prevY := y;
      // ghost var prevS := s;
      while b && y == 0
        // invariant Monad.Result(z, s) ==
        // invariant Model.SampleTailRecursive(scale, prevB, prevY)(old(s)) == Model.SampleTailRecursive(scale, b, y)(s)
        decreases *
      {
        // prevB := b;
        // prevY := y;
        // prevS := s;
        // label L1:
        var u := UniformSample(scale.numer);
        // assert (u, s) == Uniform.Model.Sample(scale.numer)(old@L1(s)).Extract();
        // label L2:
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        // assert (d, s) == BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(old@L2(s)).Extract();
        //assert Model.SampleTailRecursive(scale, b', y')(old@L1(s)) == Model.SampleTailRecursive(scale, b, y)(s);
        if d {
          // label L3:
          var a := true;
          var v := 0;
          while a
            // invariant Model.SampleTailRecursiveHelper(scale)(old@L3(s)) == Model.SampleTailRecursiveHelper(scale, v, a)(s)
            decreases *
          {
            a := BernoulliExpNegSample(Rationals.Int(1));
            if a {
              v := v + 1;
            }
          }
          // assert (v, s) == Model.SampleTailRecursiveHelper(scale)(old@L3(s)).Extract();
          var x := u + scale.numer * v;
          y := x / scale.denom;
          // label L4:
          b := CoinSample();
          // assert Coin.Model.Sample(old@L4(s)) == Monad.Result(b, s);
        }
      }
      z := if b then -y else y;
      assume {:axiom} false;
    }

  }
}
