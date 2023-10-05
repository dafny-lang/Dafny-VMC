/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../UniformPowerOfTwo/UniformPowerOfTwo.dfy"
include "Interface.dfy"
include "Model.dfy"

module UniformExtern {

  method {:extern "DRandomUniform", "Uniform"} ExternUniformSample(n: nat) returns (u: nat)

}

module Uniform.Implementation {
  import UniformPowerOfTwo
  import Model
  import Interface
  import UniformExtern

  trait {:termination false} TraitFoundational extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := UniformPowerOfTwoSample(n-1);
      while u >= n
        decreases *
        invariant Model.Sample(n)(old(s)) == UniformPowerOfTwo.Model.Sample(n-1)(old(s))
        invariant (u, s) == UniformPowerOfTwo.Model.Sample(n-1)(old(s))
      {
        u := UniformPowerOfTwoSample(n-1);
      }
    }
  }

  trait {:termination false} TraitExtern extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == (u, s)
    {
      u := UniformExtern.ExternUniformSample(n);
      assume {:axiom} false;
    }
  }
}
