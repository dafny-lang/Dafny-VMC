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

  // Only here because of #2500. Should really be imported from separate file.
  trait DRandomTrait {
    ghost var s: RNG

    method Coin() returns (b: bool)
      modifies this
      ensures CoinModel(old(s)) == (b, s)

    // 0 <= u < n
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires 0 < n
      ensures u < n
      ensures UniformModel(n)(old(s)) == (u, s)

    // a <= u < b
    method UniformInterval(a: int, b: int) returns (u: int)
      modifies this
      decreases *
      requires a < b
      ensures a <= u < b
      ensures UniformIntervalModel(a, b)(old(s)) == (u, s)

    method Geometric() returns (c: nat)
      modifies this
      decreases *
      ensures !old(s)(c)
      ensures forall i | 0 <= i < c :: old(s)(i)
      ensures s == IterateTail(old(s), c + 1)

    method BernoulliRational(m: nat, n: nat) returns (c: bool)
      modifies this
      decreases *
      requires n != 0
      requires m <= n
      ensures BernoulliRationalModel(m, n)(old(s)) == (c, s)

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

    // Uniform on {0, ..., k - 1} where k is the smallest power of 2 that is greater than n
    method Unif(n: nat) returns (u: nat)
      modifies this
      ensures UnifModel(n)(old(s)) == (u, s)
    {
      var k := 1;
      u := 0;

      while k <= n
        decreases 2*n - k
        invariant k >= 1
        invariant UnifAlternativeModel(n)(old(s)) == UnifAlternativeModel(n, k, u)(s)
      {
        var b := Coin();
        k := 2*k;
        u := if b then 2*u + 1 else 2*u;
      }
    }

    // Uniform on {0, ..., n - 1}
    method Uniform(n: nat) returns (u: nat)
      modifies this
      decreases *
      requires n > 0
      ensures u < n
      ensures UniformModel(n)(old(s)) == (u, s)
    {
      assume {:axiom} false;
      u := Unif(n-1);
      while u >= n
        decreases *
        invariant UniformModel(n)(old(s)) == UnifModel(n-1)(old(s))
        invariant (u, s) == UnifModel(n-1)(old(s))
      {
        u := Unif(n-1);
      }
    }

    method UniformInterval(a: int, b: int) returns (u: int)
      modifies this
      decreases *
      requires a < b
      ensures a <= u < b
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

    method BernoulliRational(m: nat, n: nat) returns (c: bool)
      modifies this
      decreases *
      requires n != 0
      requires m <= n
      ensures BernoulliRationalModel(m, n)(old(s)) == (c, s)
    {
      var k := Uniform(n);
      c := k < m;
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

    // Based on Algorithm 1 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method BernoulliExpNeg(gamma: real) returns (c: bool)
      modifies this
      decreases *
      requires gamma >= 0.0
    {
      if gamma <= 1.0 {
        var k := 1;
        var a := Bernoulli(gamma / (k as real));
        while a
          decreases *
        {
          k := k + 1;
          a := Bernoulli(gamma / (k as real));
        }
        c := k % 2 == 1;
      } else {
        var k := 1;
        while k <= gamma.Floor {
          var b := BernoulliExpNeg(1.0);
          if !b {
            return false;
          }
          k := k + 1;
        }
        c:= BernoulliExpNeg(gamma - gamma.Floor as real);
      }
    }

    // Based on Algorithm 2 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    method DiscreteLaplace(s: nat, t: nat) returns (z: int)
      modifies this
      requires s >= 1
      requires t >= 1
      decreases *
    {
      var b := true;
      var y := 0;
      while b && y == 0
        decreases *
      {
        var u := Uniform(t);
        var d := BernoulliExpNeg(u as real / t as real);
        if !d {
          continue;
        }
        var v := 0;
        var a := true;
        while a
          decreases *
        {
          a := BernoulliExpNeg(1.0);
          if a {
            v := v + 1;
          }
        }
        var x := u + t * v;
        y := x / s;
        b := Bernoulli(0.5);
      }
      z := if b then -y else y;
    }

    // Based on Algorithm 3 in https://arxiv.org/pdf/2004.00010.pdf; unverified
    // Note that we take sigma as a parameter, not sigma^2, to avoid square roots.
    method DiscreteGaussian(sigma: real) returns (y: int)
      modifies this
      requires sigma > 0.0
      decreases *
    {
      var t := sigma.Floor + 1;
      while true
        decreases *
      {
        y := DiscreteLaplace(1, t);
        var y_abs := if y < 0 then -y else y;
        var numerator_term := y_abs as real - sigma * sigma / t as real;
        var c := BernoulliExpNeg(numerator_term * numerator_term / 2.0 / sigma / sigma);
        if c {
          return;
        }
      }
    }
  }
}