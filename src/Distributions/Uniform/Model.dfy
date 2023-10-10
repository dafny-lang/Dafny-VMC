/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import MeasureTheory
  import Helper
  import RandomNumberGenerator
  import Quantifier
  import Monad
  import Independence
  import WhileAndUntil
  import UniformPowerOfTwo

  // Definition 49
  ghost function Sample(n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    WhileAndUntil.ProbUntil(Proposal(n), Accept(n))
  }

  function Proposal(n: nat): Monad.Hurd<nat>
    requires n > 0
  {
    UniformPowerOfTwo.Model.Sample(2 * n)
  }

  function Accept(n: nat): nat -> bool
    requires n > 0
  {
    (m: nat) => m < n
  }

  ghost function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    Monad.Map(x => a + x, Sample(b - a))
  }
}
