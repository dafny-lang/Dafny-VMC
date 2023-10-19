/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Correctness {
  import Rationals
  import Exponential
  import Rand
  import Independence
  import Model

  lemma {:axiom} Correctness(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    ensures Rand.prob(iset s | Model.Sample(gamma)(s).value) == Exponential.Exp(-Rationals.ToReal(gamma))

  lemma {:axiom} SampleIsIndep(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    ensures Independence.IsIndep(Model.Sample(gamma))
}
