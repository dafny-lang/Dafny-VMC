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
  opaque ghost function {:axiom} Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n > 0
    ensures Independence.IsIndep(h)
    ensures forall s :: 0 <= h(s).value < n

  ghost function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    Monad.Map(Sample(b - a), x => a + x)
  }

  /*******
   Lemmas
  *******/

  lemma SampleBound(n: nat, s: Rand.Bitstream)
    requires n > 0
    ensures 0 <= Sample(n)(s).value < n
  {}

  lemma IntervalSampleBound(a: int, b: int, s: Rand.Bitstream)
    requires a < b
    ensures a <= IntervalSample(a, b)(s).value < b
  {
    SampleBound(b-a, s);
  }

}
