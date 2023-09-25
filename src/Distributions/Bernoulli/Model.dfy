/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BernoulliModel {
  import opened MeasureTheory
  import opened Monad

  // Equation (4.23)
  function ProbBernoulli(p: Probability): Hurd<bool> {
    assume {:axiom} false;
    var f :=
      (b: bool) =>
        if b then
          if p <= 0.5 then
            Return(false)
          else
            ProbBernoulli(2.0 * p - 1.0)
        else
          if p <= 0.5 then
            ProbBernoulli(2.0 * p)
          else
            Return(true);
    Bind(Deconstruct, f)
  }
}
