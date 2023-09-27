/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BernoulliModel {
  import MeasureTheory
  import Monad

  // Equation (4.23)
  function ProbBernoulli(p: MeasureTheory.Probability): Monad.Hurd<bool> {
    assume {:axiom} false;
    var f :=
      (b: bool) =>
        if b then
          if p <= 0.5 then
            Monad.Return(false)
          else
            ProbBernoulli(2.0 * p - 1.0)
        else
          if p <= 0.5 then
            ProbBernoulli(2.0 * p)
          else
            Monad.Return(true);
    Monad.Bind(Monad.Deconstruct, f)
  }
}
