/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module DiscreteLaplace.Correctness {

  import Rationals
  import Exponential
  import Rand
  import Model
  import Monad
  import RealArith

  ghost function Numerator1(scale: Rationals.Rational): real
    requires scale.numer >= 1
  {
    Exponential.Exp((1.0 / scale.ToReal()) - 1.0)
  }

  ghost function Numerator2(scale: Rationals.Rational, x: int): real
    requires scale.numer >= 1
  {
    Exponential.Exp(-((RealArith.Abs(x as real)) / scale.ToReal()))
  }

  ghost function Denominator(scale: Rationals.Rational): (r: real)
    requires scale.numer >= 1
    ensures r > 0.0
  {
    var x := (1.0 / scale.ToReal()) + 1.0;
    Exponential.Positive(x);
    Exponential.Exp(x)
  }

  // Based on Definition 28 in https://arxiv.org/pdf/2004.00010.pdf
  lemma {:axiom} Correctness(scale: Rationals.Rational, x: int)
    requires scale.numer >= 1
    ensures Rand.prob(iset s | Model.Sample(scale)(s).Equals(x)) == (Numerator1(scale) * Numerator2(scale, x)) / Denominator(scale)

}
