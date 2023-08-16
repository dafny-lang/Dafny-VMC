/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Model/RandomNumberGenerator.dfy"
include "Model/Model.dfy"

module RandomTrait {
  import opened RandomNumberGenerator
  import Model

  trait {:termination false} RandomTrait {
    ghost var s: RNG

    method Coin() returns (b: bool)
      ensures Model.Coin(old(s)) == (b, s)
  //  ensures forall b :: mu(iset s | Model.Coin(s).0 == b) == 0.5

    method Uniform(n: nat) returns (u: nat)
      requires 0 < n
      ensures Model.Uniform(n)(old(s)) == (u, s)
  //  ensures forall i | 0 <= i < n :: mu(iset s | Model.Uniform(n)(s).0 == i) == 1.0 / (n as real)

    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)
  //  ensures forall i | a <= i < b :: mu(iset s | Model.UniformInterval(a, b)(s).0 == i) == 1.0 / ((b - a) as real)

    method Bernoulli(p: real) returns (c: bool) 
      decreases *            
      requires 0.0 <= p <= 1.0
      ensures Model.Bernoulli(p)(old(s)) == (c, s) 
  //  ensures mu(iset s | Model.Bernoulli(p)(s).0) == p
  }
}
