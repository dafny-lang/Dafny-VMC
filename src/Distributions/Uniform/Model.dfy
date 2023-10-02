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
  function UniformSample(n: nat): Hurd<nat>
    requires n > 0
  {
    UniformPowerOfTwoSampleTerminates(n);
    ProbUntil(UniformPowerOfTwoSample(n-1), (x: nat) => x < n)
  }

  function UniformIntervalSample(a: int, b: int): (f: Hurd<int>)
    requires a < b
  {
    (s: RNG) =>
      var (x, s') := UniformSample(b - a)(s);
      (a + x, s')
  }
}
