/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Rand {
  import Measures

  /************
   Definitions
  ************/

  type Bitstream = nat -> bool

  ghost const eventSpace: iset<iset<Bitstream>>

  ghost const prob: iset<Bitstream> -> real

  // Equation (2.37)
  function Head(s: Bitstream): bool {
    s(0)
  }

  // Equation (2.38)
  function Tail(s: Bitstream): (s': Bitstream) {
    (n: nat) => s(n+1)
  }

  function IterateTail(s: Bitstream, n: nat): (t: Bitstream)
    ensures t(0) == s(n)
  {
    if n == 0 then s else IterateTail(Tail(s), n - 1)
  }

  lemma TailOfIterateTail(s: Bitstream, n: nat)
    ensures Tail(IterateTail(s, n)) == IterateTail(s, n + 1)
  {}

  // Equation (2.41)
  function Drop(n: nat, s: Bitstream): (s': Bitstream)
    ensures Head(s') == s(n)
  {
    if n == 0 then s else Drop(n - 1, Tail(s))
  }

  /*******
   Lemmas
  *******/

   lemma {:axiom} ProbIsProbabilityMeasure()
    ensures Measures.IsProbability(eventSpace, prob)

}
