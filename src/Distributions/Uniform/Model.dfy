/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import Measures
  import NatArith
  import Rand
  import Monad
  import Independence
  import UniformPowerOfTwo

  /************
   Definitions
  ************/

  // Definition 49
  ghost function {:axiom} Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n > 0
    ensures Independence.IsIndepFunction(h)
    ensures Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => h(s).rest)
    ensures forall s :: 0 <= h(s).value < n
    ensures forall i | 0 <= i < n ::
              var e := iset s | h(s).Equals(i);
              && e in Rand.eventSpace
              && Rand.prob(e) == 1.0 / (n as real)

  ghost function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    Monad.Map(Sample(b - a), x => a + x)
  }

}
