/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// RUN: %verify "%s"

include "Model/RandomNumberGenerator.dfy"
include "Model/Model.dfy"
include "Model/Monad.dfy"
include "Model/Bernoulli.dfy"
include "Model/Uniform.dfy"

module {:extern "DafnyLibraries"} DafnyLibraries {
  import opened RandomNumberGenerator
  import opened Monad
  import opened Bernoulli
  import opened Model
  import opened Helper

  // Only here because of #2500. Should really be imported from separate file.
  trait DRandomTrait {
    ghost var s: RNG

    method Coin() returns (b: bool)
      modifies this
      ensures CoinModel(old(s)) == (b, s)

    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires 0 < n
      ensures UniformModel(n)(old(s)) == (u, s)

    method UniformInterval(a: int, b: int) returns (u: int)
      modifies this
      decreases *
      requires a < b
      ensures UniformIntervalModel(a, b)(old(s)) == (u, s)

    method Geometric() returns (c: nat)
      modifies this
      decreases *
      ensures !old(s)(c)
      ensures forall i | 0 <= i < c :: old(s)(i)
      ensures s == IterateTail(old(s), c + 1)

    method Bernoulli(p: real) returns (c: bool) 
      modifies this
      decreases *            
      requires 0.0 <= p <= 1.0
      ensures BernoulliModel(p)(old(s)) == (c, s) 
  }

  class {:extern} DRandom extends DRandomTrait {
    constructor {:extern} ()
    
    method {:extern} Coin() returns (b: bool)
      modifies this
      ensures CoinModel(old(s)) == (b, s)
    
    method UniformPowerOfTwo(exponent: nat) returns (u: nat)
      modifies this
      ensures UniformModel(Power(2, exponent))(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := 0;
      for i := 0 to exponent {
        var b := Coin();
        u := 2 * u + if b then 1 else 0;
      }
    }

    // Based on https://arxiv.org/pdf/1304.1916.pdf; unverified.
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures UniformModel(n)(old(s)) == (u, s)
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
      decreases *
      requires a < b
      ensures UniformIntervalModel(a, b)(old(s)) == (u, s)
    {
      var v := Uniform(b - a);
      assert UniformModel(b-a)(old(s)) == (v, s);
      assert UniformIntervalModel(a, b)(old(s)) == (a + v, s);
      u := a + v;
    }

    method Geometric() returns (c: nat)
      modifies this
      decreases *
      ensures !old(s)(c)
      ensures forall i | 0 <= i < c :: old(s)(i)
      ensures s == IterateTail(old(s), c + 1)
    {
      c := 0;
      var b := Coin();
      assert old(s)(c) == b;
      assert s == IterateTail(old(s), c + 1);
      while b 
        decreases *
        invariant s == IterateTail(old(s), c + 1)
        invariant b == IterateTail(old(s), c)(0)
        invariant b == old(s)(c)
        invariant forall i | 0 <= i < c :: old(s)(i)
      {
        var s' := s;
        var c' := c;
        var b' := b;
        assert forall i | 0 <= i < c' :: old(s)(i);
        assert s' == IterateTail(old(s), c' + 1);
        assert b' == IterateTail(old(s), c')(0);
        b := Coin();
        assert (b, s) == (Head(s'), Tail(s'));
        assert b == IterateTail(old(s), c' + 1)(0);
        assert s == Tail(IterateTail(old(s), c' + 1));
        TailOfIterateTail(old(s), c' + 1);
        assert s == IterateTail(old(s), (c' + 1) + 1);
        c := c + 1;
        assert c == c' + 1;
        assert old(s)(c') by {
          assert b';
        }
        assert s == IterateTail(old(s), c + 1);
        assert b == IterateTail(old(s), c)(0);
      }
    } 

    method Bernoulli(p: real) returns (c: bool)
      modifies this 
      decreases *
      requires 0.0 <= p <= 1.0
      ensures BernoulliModel(p)(old(s)) == (c, s)
    {
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

      while true
        invariant BernoulliModel(p)(old(s)) == BernoulliModel(q)(s)
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