/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Equivalence {
  import Model
  import Rand
  import Monad
  import opened Pos

  ghost predicate LoopInvariant<T>(prevI: nat32, i: nat32, a: array<T>, prevASeq: seq<T>, oldASeq: seq<T>, oldS: Rand.Bitstream, prevS: Rand.Bitstream, s: Rand.Bitstream)
    reads a
  {
    && prevI as nat <= |prevASeq|
    && i as nat <= a.Length - 1
    && Model.Shuffle(oldASeq)(oldS) == Model.Shuffle(prevASeq, prevI as nat)(prevS)
    && Model.Shuffle(prevASeq, prevI as nat)(prevS) == Model.Shuffle(a[..], i as nat)(s)
  }

  lemma ShuffleElseClause<T>(a: array<T>, oldASeq: seq<T>, oldS: Rand.Bitstream, s: Rand.Bitstream)
    requires aLength: a.Length <= 1
    requires aInvariant: oldASeq == a[..]
    requires sInvariant: oldS == s
    ensures Model.Shuffle(oldASeq)(oldS) == Monad.Result(a[..], s)
  {
    calc {
      Model.Shuffle(oldASeq)(oldS);
      { reveal aInvariant; reveal sInvariant; }
      Model.Shuffle(a[..])(s);
      Model.ShuffleCurried(a[..], s);
      { reveal aLength; assert |a[..]| == a.Length; }
      Monad.Return(a[..])(s);
      Monad.Result(a[..], s);
    }
  }
}