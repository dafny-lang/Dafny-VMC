/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Rand {
  import Measures

  /************
   Definitions
  ************/

  codatatype Bitstream = Decompose(head: bool, tail: Bitstream)

  ghost const eventSpace: iset<iset<Bitstream>>

  ghost const prob: iset<Bitstream> -> real

  // Equation (2.37)
  function Head(s: Bitstream): bool {
    s.head
  }

  // Equation (2.38)
  function Tail(s: Bitstream): (s': Bitstream) {
    s.tail
  }

  // Equation (2.41)
  function Drop(n: nat, s: Bitstream): (s': Bitstream) {
    if n == 0 then s else Drop(n - 1, Tail(s))
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} ProbIsProbabilityMeasure()
    ensures Measures.IsProbability(eventSpace, prob)

  // Equation (2.68) && (2.77)
  lemma {:axiom} CoinHasProbOneHalf(b: bool)
    ensures
      var e := (iset s | Head(s) == b);
      && e in eventSpace
      && prob(e) == 0.5

  // Equation (2.82)
  lemma {:axiom} MeasureHeadDrop(n: nat, s: Bitstream)
    ensures
      && (iset s | Head(Drop(n, s))) in eventSpace
      && prob(iset s | Head(Drop(n, s))) == 0.5

  // Equation (2.78)
  lemma {:axiom} TailIsMeasurePreserving()
    ensures Measures.IsMeasurePreserving(eventSpace, prob, eventSpace, prob, Tail)
}
