/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Uniform/Model.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BernoulliModel {
  import UniformModel
  import Monad

  // Footnote 5, p. 82
  function ProbBernoulli(numer: nat, denom: nat): (f: Monad.Hurd<bool>)
    requires denom != 0
    requires numer <= denom
    ensures forall s :: f(s).0 == (UniformModel.ProbUniform(denom)(s).0 < numer)
    ensures forall s :: f(s).1 == UniformModel.ProbUniform(denom)(s).1
  {
    Monad.Bind(UniformModel.ProbUniform(denom), (k: nat) => Monad.Return(k < numer))
  }

}
