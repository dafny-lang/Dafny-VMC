/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Equivalence {
  import Rand
  import Monad
  import Rationals
  import BernoulliExpNeg
  import Uniform
  import Coin
  import Model

  /************
   Definitions
  ************/

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
          var (v, s) :- SampleTailRecursiveHelper()(s);
          var x := u + scale.numer * v;
          var y := x / scale.denom;
          var sample := Coin.Model.Sample(s);
          SampleTailRecursive(scale, sample.value, y)(sample.rest)
        else
          SampleTailRecursive(scale, b, y)(s)

  }

  ghost function SampleTailRecursiveHelper(a: bool := true, v: int := 0): Monad.Hurd<int> {
    assume {:axiom} false; // assume termination
    (s: Rand.Bitstream) =>
      if !a then
        Monad.Result(v, s)
      else
        var (a, s) :- BernoulliExpNeg.Model.Sample(Rationals.Int(1))(s);
        SampleTailRecursiveHelper(a, if a then v + 1 else v)(s)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} SampleTailRecursiveEquivalence(scale: Rationals.Rational, s: Rand.Bitstream)
    requires scale.numer >= 1
    ensures SampleTailRecursive(scale)(s) == Model.Sample(scale)(s)
}