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
  import GeometricModel

  /*******
   Lemmas
  *******/
  
  // Equation (4.19)
  lemma {:axiom} ProbGeometricIsIndepFn()
    ensures Independence.IsIndepFn(GeometricModel.ProbGeometric())

  // Equation (4.20)
  lemma {:axiom} ProbGeometricCorrectness(n: nat)
    ensures
      var e := iset s | GeometricModel.ProbGeometric()(s).0 == n;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == Helper.RealPower(1.0 / 2.0, n + 1)
}