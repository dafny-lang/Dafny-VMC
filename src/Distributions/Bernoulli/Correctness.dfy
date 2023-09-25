/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "Model.dfy"

import opened MeasureTheory
import opened Independence
import opened BernoulliModel
import opened RandomNumberGenerator

lemma {:axiom} ProbBernoulliIsIndepFn(p: Probability)
  ensures IsIndepFn(ProbBernoulli(p))

lemma {:axiom} BernoulliCorrectness(p: Probability)
  ensures
    var e := iset s | ProbBernoulli(p)(s).0;
    && e in event_space
    && mu(e) == p
