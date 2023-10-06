/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Implementation {
  import UniformPowerOfTwo
  import Model
  import Interface

  trait {:termination false} TraitFoundational extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == (u, s)
    {
      ghost var prev_s := s;
      u := UniformPowerOfTwoSample(2 * n);
      while u >= n
        decreases *
        invariant Model.Sample(n)(old(s)) == Model.Sample(n)(prev_s)
        invariant (u, s) == Model.Proposal(n)(prev_s)
      {
        prev_s := s;
        u := UniformPowerOfTwoSample(2 * n);
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
      ensures Model.Sample(n)(old(s)) == (u, s)
    {
      u := ExternUniformSample(n);
      assume {:axiom} false;
    }
  }
}
