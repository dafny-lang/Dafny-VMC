/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Implementation {
  import Model
  import Interface

  trait {:termination false} Trait extends Interface.Trait {
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      modifies this
      ensures Model.Sample(n)(old(s)) == (u, s)
    {
      u := 0;
      var n' := n;

      while n' > 0
        invariant Model.SampleTailRecursive(n)(old(s)) == Model.SampleTailRecursive(n', u)(s)
      {
        var b := CoinSample();
        u := if b then 2*u + 1 else 2*u;
        n' := n' / 2;
      }
      Model.SampleCorrespondence(n, old(s));
    }
  }
}
