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
  import opened Pos

  trait {:termination false} Trait extends Interface.Trait {

    method Shuffle<T>(a: array<T>)
      decreases *
      modifies `s, a
      requires a.Length < 0x8000_0000
      ensures Model.Shuffle(old(a[..]))(old(s)) == Monad.Result(a[..], s)
    {
      ghost var prevI, prevASeq, prevS := 0 as int32, a[..], s; // ghost

      if (a.Length as nat32) > (1 as nat32) {
        for i: nat32 := (0 as nat32) to (a.Length as nat32) - (1 as nat32)
          invariant Equivalence.LoopInvariant(prevI, i, a, prevASeq, old(a[..]), old(s), prevS, s) // ghost
        {
          prevI, prevASeq, prevS := i, a[..], s; // ghost
          var j := UniformIntervalSample32(i, a.Length as nat32, a);
          assert prevASeq == a[..]; // ghost
          Swap(a, i, j);
          assert Equivalence.LoopInvariant(prevI, i+1, a, prevASeq, old(a[..]), old(s), prevS, s); // ghost
        }
      } else {
        Equivalence.ShuffleElseClause(a, old(a[..]), old(s), s); // ghost
      }

    }

    method Swap<T>(a: array<T>, i: nat32, j: nat32)
      modifies a
      requires i <= j
      requires 0 <= i as nat < a.Length
      requires 0 <= j as nat < a.Length
      ensures Model.Swap(old(a[..]), i as nat, j as nat) == a[..]
      ensures old(s) == s
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}
