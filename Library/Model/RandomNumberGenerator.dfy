/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "MeasureTheory.dfy"

module RandomNumberGenerator {
  import opened MeasureTheory

  /************
   Definitions  
  ************/

  predicate {:axiom} IsRNG(s: nat -> bool)

  type RNG = s: nat -> bool | IsRNG(s) witness *

  ghost const sample_space: iset<RNG> := iset s: RNG | true

  ghost const event_space: iset<iset<RNG>>

  ghost const mu: iset<RNG> -> real

  /*******
   Lemmas  
  *******/

  lemma {:axiom} RNGHasMeasure()
    ensures IsMeasure(event_space, sample_space, mu) 
}