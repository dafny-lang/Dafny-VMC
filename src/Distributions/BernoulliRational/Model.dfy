/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../Uniform/Model.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BernoulliRationalModel {
  import opened UniformModel
  import opened Monad

  // Footnote 5, p. 82
  function ProbBernoulliRational(m: nat, n: nat): (f: Hurd<bool>)
    requires n != 0
    requires m <= n
    ensures forall s :: f(s).0 == (ProbUniform(n)(s).0 < m)
    ensures forall s :: f(s).1 == ProbUniform(n)(s).1
  {
    Bind(ProbUniform(n), (k: nat) => Return(k < m))
  }

}
