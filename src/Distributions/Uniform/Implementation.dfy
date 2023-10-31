/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Uniform.Implementation {
  import Monad`Spec
  import UniformPowerOfTwo
  import Model
  import Interface
  import Equivalence

  trait {:termination false} TraitFoundational extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == Monad.Return(u)(s)
    {
      ghost var prevS := s;
      u := UniformPowerOfTwoSample(2 * n);
      while u >= n
        decreases *
        invariant Model.Sample(n)(old(s)) == Model.Sample(n)(prevS)
        invariant Monad.Return(u)(s) == Model.Proposal(n)(prevS)
      {
        Equivalence.SampleUnroll(n, prevS);
        prevS := s;
        u := UniformPowerOfTwoSample(2 * n);
      }
      reveal Model.Sample();
    }
  }

  method {:extern "DRandomUniform", "Uniform"} ExternUniformSample(n: nat) returns (u: nat)

  trait {:termination false} TraitExtern extends Interface.Trait {
    method UniformSample(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures Model.Sample(n)(old(s)) == Monad.Return(u)(s)
    {
      u := ExternUniformSample(n);
      assume {:axiom} false; // assume correctness of extern implementation
    }
  }
}
