/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Random {
  import Measures

  /************
   Definitions
  ************/

  type Bitstream = nat -> bool

  ghost const sampleSpace: iset<Bitstream> := iset s: Bitstream

  ghost const eventSpace: iset<iset<Bitstream>>

  ghost function Prob(event: iset<Bitstream>): real

  /*******
   Lemmas
  *******/

  lemma {:axiom} ProbIsProbabilityMeasure()
    ensures Measures.IsProbability(eventSpace, sampleSpace, Prob)
}
