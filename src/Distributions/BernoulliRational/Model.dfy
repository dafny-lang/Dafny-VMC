/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Uniform/Model.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BernoulliRationalModel {
  import UniformModel
  import Monad

  // Footnote 5, p. 82
  function ProbBernoulliRational(m: nat, n: nat): (f: Monad.Hurd<bool>)
    requires n != 0
    requires m <= n
    ensures forall s :: f(s).0 == (UniformModel.ProbUniform(n)(s).0 < m)
    ensures forall s :: f(s).1 == UniformModel.ProbUniform(n)(s).1
  {
    Monad.Bind(UniformModel.ProbUniform(n), (k: nat) => Monad.Return(k < m))
  }

}
