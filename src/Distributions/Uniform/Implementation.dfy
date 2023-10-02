/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../UniformPowerOfTwo/UniformPowerOfTwo.dfy"
include "Interface.dfy"
include "Model.dfy"

module UniformImplementation {
  import UniformPowerOfTwo
  import Model = UniformModel
  import Interface = UniformInterface

  trait {:termination false} TraitFoundational extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.UniformSample(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := UniformPowerOfTwoSample(n-1);
      while u >= n
        decreases *
        invariant Model.UniformSample(n)(old(s)) == UniformPowerOfTwo.Model.UniformPowerOfTwoSample(n-1)(old(s))
        invariant (u, s) == UniformPowerOfTwo.Model.UniformPowerOfTwoSample(n-1)(old(s))
      {
        u := UniformPowerOfTwoSample(n-1);
      }
    }
  }

  method {:extern "DRandomUniform", "Uniform"} ExternUniformSample(n: nat) returns (u: nat)

  trait {:termination false} TraitExtern extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.UniformSample(n)(old(s)) == (u, s)
    {
      u := ExternUniformSample(n);
      assume {:axiom} false;
    }
  }
}
