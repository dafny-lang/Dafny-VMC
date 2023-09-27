/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/Helper.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "Model.dfy"

import opened WhileAndUntil
import opened Independence
import opened RandomNumberGenerator
import opened Quantifier

lemma ProbWhileGeometricTerminates()
  ensures
    var fst := (t: (bool, nat)) => t.0;
    ProbWhileTerminates(ProbGeometricIter, fst)
{
  var fst := (t: (bool, nat)) => t.0;
  assert forall t :: IsIndepFn(ProbGeometricIter(t));
  assert forall t :: ExistsStar(WhileAndUntil.Helper(ProbGeometricIter, fst, t)) by {
    assume {:axiom} false;
  }
  EnsureProbWhileTerminates(ProbGeometricIter, fst);
}

// Equation (4.19)
lemma {:axiom} ProbGeometricIsIndepFn()
  ensures IsIndepFn(ProbGeometric())

// Equation (4.20)
lemma {:axiom} ProbGeometricCorrectness(n: nat)
  ensures
    var e := iset s | ProbGeometric()(s).0 == n;
    && e in event_space
    && mu(e) == Helper.RealPower(0.5, n + 1)
