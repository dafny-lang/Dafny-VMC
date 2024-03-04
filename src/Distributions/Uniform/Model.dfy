/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Model {
  import Measures
  import NatArith
  import Rand
  import Quantifier
  import Monad
  import Independence
  import Loops
  import UniformPowerOfTwo

  /************
   Definitions
  ************/

  // Definition 49
  opaque ghost function {:axiom} Sample(n: nat): Monad.Hurd<nat>
    requires n > 0

  ghost function IntervalSample(a: int, b: int): (f: Monad.Hurd<int>)
    requires a < b
  {
    Monad.Map(Sample(b - a), x => a + x)
  }

  /*******
   Lemmas
  *******/

  
  lemma {:axiom} SampleBound(n: nat, s: Rand.Bitstream)
    requires n > 0
    requires Sample(n)(s).Result?
    ensures 0 <= Sample(n)(s).value < n

  lemma IntervalSampleBound(a: int, b: int, s: Rand.Bitstream)
    requires a < b
    requires IntervalSample(a, b)(s).Result?
    ensures a <= IntervalSample(a, b)(s).value < b
  {
    SampleBound(b-a, s);
  }

}
