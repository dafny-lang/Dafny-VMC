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

import opened WhileAndUntil
import opened Independence
import opened RandomNumberGenerator

lemma {:axiom} ProbWhileGeometricTerminates()
  ensures
    var fst := (t: (bool, int)) => t.0;
    ProbWhileTerminates(ProbGeometricIter, fst)

// Equation (4.19)
lemma {:axiom} ProbGeometricIsIndepFn()
  ensures IsIndepFn(ProbGeometric())

// Equation (4.20)
lemma {:axiom} ProbGeometricCorrectness(n: nat)
  ensures
    var e := iset s | ProbGeometric()(s).0 == n;
    && e in event_space
    && mu(e) == Helper.RealPower(1.0 / 2.0, n + 1)
