/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "Model.dfy"

lemma {:axiom} ProbBernoulliIsIndepFn(p: MeasureTheory.Probability)
  ensures Independence.IsIndepFn(BernoulliModel.ProbBernoulli(p))

lemma {:axiom} BernoulliCorrectness(p: MeasureTheory.Probability)
  ensures
    var e := iset s | BernoulliModel.ProbBernoulli(p)(s).0;
    && e in RandomNumberGenerator.event_space
    && RandomNumberGenerator.mu(e) == p
