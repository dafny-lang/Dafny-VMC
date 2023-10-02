/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "../UniformPowerOfTwo/Model.dfy"

module UniformModel {
  import opened RandomNumberGenerator
  import opened Quantifier
  import opened Monad
  import opened Independence
  import opened WhileAndUntil
  import opened UniformPowerOfTwoModel

  // Definition 49
  function ProbUniform(n: nat): Hurd<nat>
    requires n > 0
  {
    ProbUnifTerminates(n);
    ProbUntil(ProbUnif(n-1), (x: nat) => x < n)
  }

  function ProbUniformInterval(a: int, b: int): (f: Hurd<int>)
    requires a < b
  {
    (s: RNG) =>
      var (x, s') := ProbUniform(b - a)(s);
      (a + x, s')
  }
}
