/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Model/RandomNumberGenerator.dfy"
include "Model/Model.dfy"
include "Model/Monad.dfy"
include "RandomTrait.dfy"
include "Model/Bernoulli.dfy"
include "Model/Uniform.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomTrait
  import opened RandomNumberGenerator
  import opened Monad
  import opened Bernoulli
  import opened Unif = Uniform
  import Model

  class {:extern} Random extends RandomTrait {
    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      modifies this
      ensures Model.Coin(old(s)) == (b, s)

    // Based on https://arxiv.org/pdf/1304.1916.pdf; unverified.
    method Uniform(n: nat) returns (u: nat)
      modifies this
      requires 0 < n
      ensures Model.Uniform(n)(old(s)) == (u, s)
      decreases *
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
      modifies this
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)
      decreases *
    {
      var v := Uniform(b - a);
      assert Model.Uniform(b-a)(old(s)) == (v, s);
      assert Model.UniformInterval(a, b)(old(s)) == (a + v, s);
      u := a + v;
    }

    method Bernoulli(p: real) returns (c: bool)
      modifies this 
      decreases *
      requires 0.0 <= p <= 1.0
      ensures Model.Bernoulli(p)(old(s)) == (c, s)
    {
      c := true;
      var end := false;
      var q: Probability := p as real;

      var b := Coin();
      if b {
        if q <= 0.5 {
          return false;
        } else {
          q := 2.0 * (q as real) - 1.0;
        }
      } else {
        if q <= 0.5 {
          q := 2.0 * (q as real); 
        } else {
          return true;
        }
      }

      while !end 
        invariant (!end && Model.Bernoulli(p)(old(s)) == Model.Bernoulli(q)(s)) || (end && Model.Bernoulli(p)(old(s)) == (c, s))
        decreases *
      {
        b := Coin();
        if b {
          if q <= 0.5 {
            return false;
          } else {
            q := 2.0 * (q as real) - 1.0;
          }
        } else {
          if q <= 0.5 {
            q := 2.0 * (q as real);
          } else {
            return true;
          }
        }
      }
    }
  }
}