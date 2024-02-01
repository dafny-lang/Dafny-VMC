/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Equivalence {
  import Model
  import Rand

  ghost predicate LoopInvariant<T>(prevI: nat, i: nat, a: array<T>, prevASeq: seq<T>, oldASeq: seq<T>, oldS: Rand.Bitstream, prevS: Rand.Bitstream, s: Rand.Bitstream)
    reads a
  {
    && prevI <= |prevASeq|
    && i <= a.Length - 1
    && Model.Shuffle(oldASeq)(oldS) == Model.Shuffle(prevASeq, prevI)(prevS)
    && Model.Shuffle(prevASeq, prevI)(prevS) == Model.Shuffle(a[..], i)(s)
  }

}