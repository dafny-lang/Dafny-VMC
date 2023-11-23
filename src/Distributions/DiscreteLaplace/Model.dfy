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
  import Loops

  ghost function Sample(scale: Rationals.Rational): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    var f := (x: (bool, int)) => if x.0 then -x.1 else x.1;
    Monad.Map(SampleLoop(scale), f)
  }

  ghost function SampleLoop(scale: Rationals.Rational): Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    Loops.While(Condition, Body(scale))((true, 0))
  }

  ghost function Body(scale: Rationals.Rational): ((bool, int)) -> Monad.Hurd<(bool, int)>
    requires scale.numer >= 1
  {
    (x: (bool, int)) => 
      (s: Rand.Bitstream) =>
        var (b, y) := (x.0, x.1); 
        var (u, s) :- Uniform.Model.Sample(scale.numer)(s);
        var (d, s) :- BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(s);
        if d then
          var (v, s) :- SampleTailRecursiveHelper(scale)(s);
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var (b, s) :- Coin.Model.Sample(s);
          Monad.Result((b, y), s)
        else 
          Monad.Result((b, y), s)
  }

  ghost function Condition(x: (bool, int)): bool {
    x.0 && x.1 == 0
  }

  ghost function SampleTailRecursive(scale: Rationals.Rational, b: bool := true, y: int := 0): Monad.Hurd<int>
    requires scale.numer >= 1
  {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !(b && y == 0) then
        Monad.Result(if b then -y else y, s)
      else
        var (u, s) :- Uniform.Model.Sample(scale.numer)(s);
        var (d, s) :- BernoulliExpNeg.Model.Sample(Rationals.Rational(u, scale.numer))(s);
        if d then
          var (v, s) :- SampleTailRecursiveHelper(scale)(s);
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var sample := Coin.Model.Sample(s);
          SampleTailRecursive(scale, sample.value, y)(sample.rest)
        else 
          SampleTailRecursive(scale, b, y)(s)

  }

  ghost function SampleTailRecursiveHelper(scale: Rationals.Rational, a: bool := true, v: int := 0): Monad.Hurd<int> {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !a then
        Monad.Result(v, s)
      else
        var (a, s) :- BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s);
        SampleTailRecursiveHelper(scale, a, if a then v + 1 else v)(s)
  }
}
