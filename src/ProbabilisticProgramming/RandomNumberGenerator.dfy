/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module RandomNumberGenerator {
  import MeasureTheory
  import Partials

  /************
   Definitions
  ************/

  predicate {:axiom} IsRNG(s: nat -> bool)

  type RNG = s: nat -> bool | IsRNG(s) witness *

  ghost const sample_space: iset<RNG> := iset s: RNG | true

  ghost const event_space: iset<iset<RNG>>

  ghost const partial_sample_space: iset<Partials.Partial<RNG>> := iset s: Partials.Partial<RNG>

  ghost const partial_event_space: iset<iset<Partials.Partial<RNG>>> := MeasureTheory.partialEventSpace(event_space)

  ghost const mu: iset<RNG> -> real

  ghost function partial_mu(event: iset<Partials.Partial<RNG>>): real {
    mu(iset s | Partials.Terminating(s) in event)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} RNGHasMeasure()
    ensures MeasureTheory.IsProbability(event_space, sample_space, mu)

  lemma PartialRngHasMeasure()
    ensures MeasureTheory.IsProbability(partial_event_space, partial_sample_space, partial_mu)
  {
    // todo
  }
}
