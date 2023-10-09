/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Correctness {
  import Rationals
  import Exponential
  import RandomNumberGenerator
  import Partial
  import Independence
  import Model

  lemma {:axiom} Correctness(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    ensures RandomNumberGenerator.mu(iset s | Model.Sample(gamma)(s).0 == Partial.Terminating(true)) == Exponential.Exp(-Rationals.ToReal(gamma))

  lemma {:axiom} SampleIsIndepFn(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    ensures Independence.IsIndepFn(Model.Sample(gamma))
}
