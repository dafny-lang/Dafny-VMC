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

  trait {:termination false} Trait extends Interface.Trait {

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplaceSample(scale: Rationals.Rational) returns (z: int)
      modifies this
      requires scale.numer >= 1
      decreases *
      ensures Monad.Result(z, s) == Model.SampleTailRecursive(scale)(old(s))
    {
      var b := true;
      var y := 0;
      ghost var b' := b;
      ghost var y' := y;
      while b && y == 0
        //invariant Model.SampleTailRecursive(scale, b', y')(old(s)) == Model.SampleTailRecursive(scale, b, y)(s)
        decreases *
      {
        b' := b;
        y' := y;
        label L1:
        var u := UniformSample(scale.numer);
        assert (u, s) == Monad.Extract(Uniform.Model.Sample(scale.numer)(old@L1(s)));
        label L2:
        var d := BernoulliExpNegSample(Rationals.Rational(u, scale.numer));
        assert (d, s) == Monad.Extract(BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(old@L2(s)));
        //assert Model.SampleTailRecursive(scale, b', y')(old@L1(s)) == Model.SampleTailRecursive(scale, b, y)(s);
        if !d {
          continue;
        }
        label L3:
        var v := 0;
        var a := true;
        while a
          invariant Model.SampleTailRecursiveHelper(scale)(old@L3(s)) == Model.SampleTailRecursiveHelper(scale, v, a)(s)
          decreases *
        {
          a := BernoulliExpNegSample(Rationals.Int(1));
          if a {
            v := v + 1;
          }
        }
        assert (v, s) == Monad.Extract(Model.SampleTailRecursiveHelper(scale)(old@L3(s)));
        var x := u + scale.numer * v;
        y := x / scale.denom;
        label L4:
        b := BernoulliSample(Rationals.Rational(1, 2));
        assert (b, s) == Monad.Extract(Bernoulli.Model.Sample(1, 2)(old@L4(s)));
        //assume {:axiom} false; // add equivalence proof later
      }
      z := if b then -y else y;
      assume {:axiom} false; // add equivalence proof later
    }

  }
}
