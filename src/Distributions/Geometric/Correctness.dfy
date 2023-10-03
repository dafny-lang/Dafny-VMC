/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Helper.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "Model.dfy"

module GeometricCorrectness {
  import Helper
  import WhileAndUntil
  import Independence
  import RandomNumberGenerator
  import Model = GeometricModel

  /*******
   Lemmas
  *******/

  // Equation (4.19)
  lemma {:axiom} SampleIsIndepFn()
    ensures Independence.IsIndepFn(Model.Sample())

  // Equation (4.20)
  lemma {:axiom} SampleCorrectness(n: nat)
    ensures
      var e := iset s | Model.Sample()(s).0 == n;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == Helper.RealPower(1.0 / 2.0, n + 1)
}