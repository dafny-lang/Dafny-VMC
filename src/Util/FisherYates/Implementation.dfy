/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Interface
  import Monad
  import Model
  import Uniform
  import Equivalence

  trait {:termination false} Trait extends Interface.Trait {

    method {:vcs_split_on_every_assert} Shuffle<T>(a: array<T>)
      decreases *
      modifies `s, a
      ensures Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s)
    {
      ghost var prevI, prevASeq, prevS := 0, a[..], s; // ghost
      if a.Length > 1 {
        for i := 0 to a.Length - 1
          invariant Equivalence.LoopInvariant(prevI, i, a, prevASeq, old(a[..]), old(s), prevS, s)
        {
          prevI, prevASeq, prevS := i, a[..], s; // ghost
          var j := UniformIntervalSample(i, a.Length);
          assert prevASeq == a[..]; // ghost
          Swap(a, i, j);
        }
      } else {
        assert prevASeq == a[..]; // ghost
      }

    }

    method Swap<T>(a: array<T>, i: nat, j: nat)
      modifies a
      requires i <= j
      requires 0 <= i < a.Length
      requires 0 <= j < a.Length
      ensures Model.Swap(old(a[..]), i, j) == a[..]
      ensures old(s) == s
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}
