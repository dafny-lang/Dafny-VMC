/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../UniformPowerOfTwo/Interface.dfy"
include "../UniformPowerOfTwo/Implementation.dfy"
include "Interface.dfy"
include "Model.dfy"

module UniformImplementation {
  import opened MeasureTheory
  import opened Monad
  import opened UniformPowerOfTwoInterface
  import opened UniformPowerOfTwoModel
  import opened UniformModel
  import opened UniformInterface

  trait {:termination false} TUniformFoundational extends IUniform {
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := UniformPowerOfTwo(n-1);
      while u >= n
        decreases *
        invariant UniformModel.ProbUniform(n)(old(s)) == UniformPowerOfTwoModel.ProbUnif(n-1)(old(s))
        invariant (u, s) == UniformPowerOfTwoModel.ProbUnif(n-1)(old(s))
      {
        u := UniformPowerOfTwo(n-1);
      }
    }
  }

  method {:extern "DRandomUniform", "Uniform"} ExternUniform(n: nat) returns (u: nat)

  trait {:termination false} TUniformExtern extends IUniform {
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel.ProbUniform(n)(old(s)) == (u, s)
    {
      u := ExternUniform(n);
      assume {:axiom} false;
    }
  }
}
