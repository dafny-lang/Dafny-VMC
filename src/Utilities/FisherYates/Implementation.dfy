/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Uniform
  import Model

  trait {:termination false} Trait extends Uniform.Interface.Trait {

    method Shuffle<T>(a: array<T>) returns (b: array<T>)
      modifies this, a
      decreases *
//    ensures Model.Shuffle(Helper.ArrayToSeq(a))(old(s)) == Monad.Result(Helper.ArrayToSeq(b), s)
    {
      for i := a.Length downto 0 {
        assert 0 <= i <= a.Length - 1;
        var j := UniformSample(i+1);
        assert 0 <= j <= i;
        Swap(a, i, j);
      }
      return a;
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