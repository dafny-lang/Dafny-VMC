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

    method Uniform(n: nat) returns (u: nat)
      requires 0 < n
      ensures Model.Uniform(n)(old(s)) == (u, s)

    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)

    method Bernoulli(p: real) returns (c: bool) 
      decreases *            
      requires 0.0 <= p <= 1.0
      ensures Model.Bernoulli(p)(old(s)) == (c, s) 
  }
}
