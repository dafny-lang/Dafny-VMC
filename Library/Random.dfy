/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Model/RandomNumberGenerator.dfy"
include "Model/Model.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomNumberGenerator
  import Model

  type Probability = x: real | 0.0 <= x <= 1.0

  class {:extern} Random {
    ghost var s: RNG

    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      ensures Model.Coin(old(s)) == (b, s)

    // Based on https://arxiv.org/pdf/1304.1916.pdf; unverified.
    method Uniform(n: nat) returns (u: nat)
      requires n > 0
      ensures Model.Uniform(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      var v := 1;
      u := 0;
      while true {
        v := 2 * v;
        var b := Coin();
        u := 2 * u + if b then 1 else 0;
        if v >= n {
          if u < n {
            return;
          } else {
            v := v - n;
            u := u - n;
          }
        }
      }
    }
    
    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)
    {
      var v := Uniform(b - a);
      u := a + v;
    }

    method Bernoulli(p: Probability) returns (c: bool) 
      //ensures Model.Bernoulli(p)(old(s)) == (c, s) 
      decreases *
    {
      var p := p as real;
      while true 
        decreases *
      {
        var b := Coin();
        //assert b  == Head(old(s));
        if b {
          if p <= 0.5 {
            c := false;
            return;
          } else {
            calc {
              1.0 >= (p as real) >= 0.5;
            ==>
              2.0 >= 2.0 * (p as real) >= 1.0;
            ==>
              1.0 >= 2.0 * (p as real) - 1.0 >= 0.0;
            }
            p := 2.0 * (p as real) - 1.0;
          }
        } else {
          if p <= 0.5 {
            p := 2.0 * (p as real);
          } else {
            c := true;
            return;
          }
        }
      }
    }
  }
}