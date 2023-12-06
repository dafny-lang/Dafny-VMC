/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Uniform
  import Model
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    method Shuffle<T>(a: array<T>)
      modifies this, a
      decreases *
      //    ensures Model.Shuffle(Helper.ArrayToSeq(old(a)))(old(s)) == Monad.Result(Helper.ArrayToSeq(a), s)
    {
      for i := a.Length downto 0 {
        assert 0 <= i <= a.Length - 1;
        var j := UniformSample(i+1);
        assert 0 <= j <= i;
        Swap(a, i, j);
      }
    }

    method Swap<T>(a: array<T>, i: nat, j: nat)
      modifies a
      requires 0 <= i < a.Length
      requires 0 <= j < a.Length
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}