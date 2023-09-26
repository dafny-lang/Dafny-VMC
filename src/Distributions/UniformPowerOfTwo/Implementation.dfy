/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "Interface.dfy"
include "Model.dfy"

module UnifImplementation {
  import opened MeasureTheory
  import opened Monad
  import opened UnifModel
  import opened UnifInterface

  trait {:termination false} TUnif extends IUnif {
    method Unif(n: nat) returns (u: nat)
      modifies this
      ensures UnifModel.UnifModel(n)(old(s)) == (u, s)
    {
      var k := 1;
      u := 0;

      while k <= n
        decreases 2*n - k
        invariant k >= 1
        invariant UnifAlternativeModel(n)(old(s)) == UnifAlternativeModel(n, k, u)(s)
      {
        var b := Coin();
        k := 2*k;
        u := if b then 2*u + 1 else 2*u;
      }
    }
  }
}
