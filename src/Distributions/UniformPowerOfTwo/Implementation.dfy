/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Implementation {
  import Monad
  import Model
  import Equivalence
  import Interface

  trait {:termination false} Trait extends Interface.Trait {
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      requires n >= 1
      modifies this
      ensures Model.Sample(n)(old(s)) == Monad.Result(u, s)
    {
      u := 0;
      var n' := n;

      while n' > 1
        invariant n' >= 1
        invariant Equivalence.SampleTailRecursive(n)(old(s)) == Equivalence.SampleTailRecursive(n', u)(s)
      {
        var b := CoinSample();
        u := if b then 2*u + 1 else 2*u;
        n' := n' / 2;
      }
      Equivalence.SampleCorrespondence(n, old(s));
    }
  }
}
