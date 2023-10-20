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


  ghost function Numerator1(scale: Rationals.Rational): real {
    Exponential.Exp((1.0 / Rationals.ToReal(scale)) - 1.0)
  }

  ghost function Numerator2(scale: Rationals.Rational, x: int): real {
    Exponential.Exp(-((RealArith.Abs(x as real)) / Rationals.ToReal(scale)))
  }

  ghost function Denominator(scale: Rationals.Rational): real {
    Exponential.Exp((1.0 / Rationals.ToReal(scale)) + 1.0)
  }

  lemma {:axiom} Correctness(scale: Rationals.Rational, x: int)
    requires scale.numer >= 1
    ensures Rand.prob(iset s | Model.Sample(scale)(s).value == x) == (Numerator1(scale) * Numerator2(scale, x)) / Denominator(scale) 

}
