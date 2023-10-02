/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "Interface.dfy"
include "Model.dfy"

module UniformPowerOfTwoImplementation {
  import Model = UniformPowerOfTwoModel
  import Interface = UniformPowerOfTwoInterface

  trait {:termination false} Trait extends Interface.Trait {
    method UniformPowerOfTwoSample(n: nat) returns (u: nat)
      modifies this
      ensures Model.UnifModel(n)(old(s)) == (u, s)
    {
      var k := 1;
      u := 0;

      while k <= n
        decreases 2*n - k
        invariant k >= 1
        invariant Model.UnifAlternativeModel(n)(old(s)) == Model.UnifAlternativeModel(n, k, u)(s)
      {
        var b := CoinSample();
        k := 2*k;
        u := if b then 2*u + 1 else 2*u;
      }
    }
  }
}
