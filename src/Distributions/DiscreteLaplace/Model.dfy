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
  import Coin

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
        var sample := Uniform.Model.Sample(scale.numer)(s);
        if sample.Result? then
          var (u, s) := (sample.value, sample.rest);
          var sample := BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(s);
          if sample.Result? then
            var (d, s) := (sample.value, sample.rest);
            if !d then
              SampleTailRecursive(scale, b, y)(s)
            else
              var sample := SampleTailRecursiveHelper(scale)(s);
              if sample.Result? then
                var (v, s) := (sample.value, sample.rest);
                var x := u + scale.numer * v;
                var y := x / scale.denom;
                var sample := Coin.Model.Sample(s);
                var (b, s) := (sample.value, sample.rest);
                SampleTailRecursive(scale, b, y)(s)
              else
                Monad.Diverging
          else
            Monad.Diverging
        else
          Monad.Diverging

  }

  ghost function SampleTailRecursiveHelper(scale: Rationals.Rational, v: int := 0, a: bool := true): Monad.Hurd<int> {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !a then
        Monad.Result(v, s)
      else
        var sample := BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s);
        if sample.Result? then
          var (a, s) := (sample.value, sample.rest);
          SampleTailRecursiveHelper(scale, if a then v + 1 else v, a)(s)
        else
          Monad.Diverging
  }

}
