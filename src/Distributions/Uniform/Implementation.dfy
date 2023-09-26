/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "Interface.dfy"
include "Model.dfy"

module UniformImplementation {
  import opened MeasureTheory
  import opened Monad
  import opened UniformModel
  import opened UniformInterface

  trait {:termination false} UniformFoundational extends IUniform {
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := Unif(n-1);
      while u >= n
        decreases *
        invariant UniformModel.ProbUniform(n)(old(s)) == UniformModel.ProbUnif(n-1)(old(s))
        invariant (u, s) == UniformModel.ProbUnif(n-1)(old(s))
      {
        u := Unif(n-1);
      }
    }
  }

  trait {:termination false} Unif extends IUnif {
    method Unif(n: nat) returns (u: nat)
      modifies this
      ensures UniformModel.UnifModel(n)(old(s)) == (u, s)
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

  trait {:termination false} UniformExtern extends IUniform {
    method {:extern} Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)
  }
}
