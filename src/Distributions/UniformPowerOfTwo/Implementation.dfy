/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "Interface.dfy"
include "Model.dfy"

module UniformPowerOfTwoImplementation {
  import UniformPowerOfTwoModel
  import UniformPowerOfTwoInterface

  trait {:termination false} TUniformPowerOfTwo extends UniformPowerOfTwoInterface.IUniformPowerOfTwo {
    method UniformPowerOfTwo(n: nat) returns (u: nat)
      modifies this
      ensures UniformPowerOfTwoModel.ProbUnif(n)(old(s)) == (u, s)
    {
      var k := 1;
      u := 0;

      while k <= n
        decreases 2*n - k
        invariant k >= 1
        invariant UniformPowerOfTwoModel.ProbUnifAlternative(n)(old(s)) == UniformPowerOfTwoModel.ProbUnifAlternative(n, k, u)(s)
      {
        var b := Coin();
        k := 2*k;
        u := if b then 2*u + 1 else 2*u;
      }
      UniformPowerOfTwoModel.ProbUnifCorrespondence(n, old(s));
    }
  }
}
