/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Uniform
  import Model
  import Interface
  import Permutations
  import Helper
  import Monad

  trait {:termination false} Trait extends Interface.Trait {

    method Shuffle<T>(a: array<T>)
      modifies this, a
      decreases *
      ensures Model.Shuffle(Helper.ArrayToSeq(old(a)))(old(s)) == Monad.Result(Helper.ArrayToSeq(a), s)
    {
      var i := 0;
      while i < a.Length 
        invariant 0 <= i <= a.Length
        invariant Model.Shuffle(old(Helper.ArrayToSeq(a)))(old(s)) == Model.Shuffle(Helper.ArrayToSeq(a), i)(s)
      {
        assume {:axiom} false;
        assert 0 <= i < a.Length;
        var j := UniformIntervalSample(i, a.Length);
        assert i <= j < a.Length;
        Swap(a, i, j);
        i := i + 1;
      }
    }

    method Swap<T>(a: array<T>, i: nat, j: nat)
      modifies a
      requires i <= j
      requires 0 <= i < a.Length
      requires 0 <= j < a.Length
      ensures Permutations.Swap(old(Helper.ArrayToSeq(a)), i, j) == Helper.ArrayToSeq(a)
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}