/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    method Shuffle<T(!new)>(a: array<T>)
      decreases *
      modifies this, a
    {
      var i := 0;
      while i < a.Length {
        var j := UniformIntervalSample(i, a.Length);
        Swap(a, i, j);
        i := i + 1;
      }
    }

    method Swap<T>(a: array<T>, i: nat, j: nat)
      modifies a
      requires i <= j
      requires 0 <= i < a.Length
      requires 0 <= j < a.Length
    {
      a[i], a[j] := a[j], a[i];
    }

  }
}