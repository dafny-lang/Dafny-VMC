/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Implementation {
  import Monad
  import UniformPowerOfTwo
  import Model
  import Interface

  trait {:termination false} TraitFoundational extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == Monad.Terminating(u, s)
    {
      ghost var prev_s := s;
      u := UniformPowerOfTwoSample(2 * n);
      while u >= n
        decreases *
        invariant Model.Sample(n)(old(s)) == Model.Sample(n)(prev_s)
        invariant Model.Proposal(n)(prev_s) == Monad.Terminating(u, s)
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
      ensures Model.Sample(n)(old(s)) == Monad.Terminating(u, s)
    {
      u := ExternUniformSample(n);
      assume {:axiom} false; // assume correctness of extern implementation
    }
  }
}
