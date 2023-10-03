/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "../UniformPowerOfTwo/UniformPowerOfTwo.dfy"

module UniformModel {
  import RandomNumberGenerator
  import Quantifier
  import Monad
  import Independence
  import WhileAndUntil
  import UniformPowerOfTwo

  // Definition 49
  function Sample(n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    UniformPowerOfTwo.Model.SampleTerminates(n);
    WhileAndUntil.ProbUntil(UniformPowerOfTwo.Model.Sample(n-1), (x: nat) => x < n)
  }

  function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    (s: RandomNumberGenerator.RNG) =>
      var (x, s') := Sample(b - a)(s);
      (a + x, s')
  }
}
