/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Implementation {
  import Interface

  trait {:termination false} Trait extends Interface.Trait {

    method Shuffle<T>(a: array<T>)
      decreases *
      modifies this, a
    {
      if a.Length > 1 {
        for i := 0 to a.Length - 1 {
          var j := UniformIntervalSample(i, a.Length);
          a[i], a[j] := a[j], a[i];
        }
      }
    }

  }
}