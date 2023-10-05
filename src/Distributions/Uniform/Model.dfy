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

module Uniform.Model {
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
    SampleTerminates(n);
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

  lemma {:axiom} SampleTerminates(n: nat)
    requires n > 0
    ensures
      && Independence.IsIndepFn(Proposal(n))
      && Quantifier.ExistsStar(WhileAndUntil.ProposalIsAccepted(Proposal(n), Accept(n)))
      && WhileAndUntil.ProbUntilTerminates(Proposal(n), Accept(n))

  function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    (s: RandomNumberGenerator.RNG) =>
      var (x, s') := Sample(b - a)(s);
      (a + x, s')
  }
}
