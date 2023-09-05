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

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomTrait
  import opened RandomNumberGenerator
  import opened Monad
  import opened Bernoulli
  import Model

  class {:extern} Random extends RandomTrait {
    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      ensures Model.Coin(old(s)) == (b, s)

    // Based on https://arxiv.org/pdf/1304.1916.pdf; unverified.
    method Uniform(n: nat) returns (m: nat)
      requires n > 0
      ensures Model.Uniform(n)(old(s)) == (m, s)
    {
      assume {:axiom} false;
      var v := 1;
      m := 0;
      while true {
        v := 2 * v;
        var b := Coin();
        m := if b then 2*m + 1 else 2*m;
        if v >= n {
          if m < n {
            return;
          } else {
            v := v - n;
            m := m - n;
          }
        }
      }
/*       while true
        decreases *
      {
        var (m, s) := ProbUnif(n-1)(s);
        if m < n {
          return (m, s);
        }
      } */
    }
    
    method UniformInterval(a: int, b: int) returns (u: int)
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (u, s)
    {
      var v := Uniform(b - a);
      u := a + v;
    }

    method Bernoulli(p: real) returns (c: bool) 
      decreases *            
      requires 0.0 <= p <= 1.0
      ensures Model.Bernoulli(p)(old(s)) == (c, s) 
    {
      c := true;

      var b := Coin();
      assert (b, s) == (Head(old(s)), Tail(old(s)));
      if b {
        if p <= 0.5 {
          c := false;
          assert Model.Bernoulli(p)(old(s)) == (c, s);
          return;
        } else {
          var p := 2.0 * (p as real) - 1.0;
        }
      } else {
        if p <= 0.5 {
          var p := 2.0 * (p as real);
        } else {
          c := true;
          assert Model.Bernoulli(p)(old(s)) == (c, s);
          return;
        }
      }

      while true 
        decreases *
        invariant (b && p <= 0.5) || (!b && p > 0.5) ==> ProbBernoulliCurried(p, old(s)) == (c, s)
      {
        label L:
        b := Coin();
        assert (b, s) == (Head(old@L(s)), Tail(old@L(s)));
        if b {
          if p <= 0.5 {
            c := false;
            assert Model.Bernoulli(p)(old@L(s)) == (c, s);
            return;
          } else {
            var p := 2.0 * (p as real) - 1.0;
          }
        } else {
          if p <= 0.5 {
            var p := 2.0 * (p as real);
          } else {
            c := true;
            assert Model.Bernoulli(p)(old@L(s)) == (c, s);
            return;
          }
        }
      }
    }
  }
}