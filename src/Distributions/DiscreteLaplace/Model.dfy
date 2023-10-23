/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Model {
  import Monad
  import Rand
  import Rationals
  import Uniform
  import BernoulliExpNeg
  import Bernoulli

  ghost function Sample(scale: Rationals.Rational): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    SampleTailRecursive(scale)
  }

  ghost function SampleTailRecursive(scale: Rationals.Rational, b: bool := true, y: int := 0): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !(b && y == 0) then
        Monad.Result(if b then -y else y, s)
      else
        var (u, s) := Monad.Extract(Uniform.Model.Sample(scale.numer)(s));
        var (d, s) := Monad.Extract(BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(s));
        if !d then
          SampleTailRecursive(scale, b, y)(s)
        else
          var (v, s) := Monad.Extract(SampleTailRecursiveHelper(scale)(s));
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var (b, s) := Monad.Extract(Bernoulli.Model.Sample(1, 2)(s));
          SampleTailRecursive(scale, b, y)(s)
  }

  ghost function SampleTailRecursiveHelper(scale: Rationals.Rational, v: int := 0, a: bool := true): Monad.Hurd<int> {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !a then
        Monad.Result(v, s)
      else
        var (a, s) := Monad.Extract(BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s));
        SampleTailRecursiveHelper(scale, if a then v + 1 else v, a)(s)
  }

}
