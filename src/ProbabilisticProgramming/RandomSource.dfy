/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Rand {
  import Measures

  /************
   Definitions
  ************/

  type Bitstream = s: nat -> bool | IsBitstream(s) witness *

  ghost predicate {:axiom} IsBitstream(stream: nat -> bool)

  ghost const sampleSpace: iset<Bitstream> := iset s: Bitstream

  ghost const eventSpace: iset<iset<Bitstream>>

  ghost const prob: iset<Bitstream> -> real

  /*******
   Lemmas
  *******/

  lemma {:axiom} ProbIsProbabilityMeasure()
    ensures Measures.IsProbability(eventSpace, sampleSpace, prob)
}
