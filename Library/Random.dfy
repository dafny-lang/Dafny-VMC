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

/*     // Based on https://arxiv.org/pdf/1304.1916.pdf; unverified.
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
      } */
/*       while true
        decreases *
      {
        var (m, s) := ProbUnif(n-1)(s);
        if m < n {
          return (m, s);
        }
      } 
    }*/

 /*    method Unif2(n: nat) returns (m: nat) 
      decreases *
      ensures Unif.ProbUnif(n)(old(s)) == (m, s)
    {
      m := 0;

      if n == 0 {
        return m;
      } else {
        var b := Coin();
        m := if b then 2*m + 1 else 2*m;
        var n := n / 2;
      }

      while true
        decreases *
        invariant m >= 0 && (n == 0 ==> Unif.ProbUnif(n)(old(s)) == (m, s))
      {
        if n == 0 {
          return m;
        } else {
          var b := Coin();
          m := if b then 2*m + 1 else 2*m;
          var n := n / 2;
        }
      }
    } */

    method {:timeLimit 20} Uniform(n: nat) returns (m: nat)
      modifies this
      requires n > 0
      ensures Model.Uniform(n)(old(s)) == (m, s)
      decreases *
    {
      assume {:axiom} false;
      m := 0;
      var n := n - 1;

      while true 
        decreases *
        invariant m >= 0 && (n == 0 && m < n ==> Model.Uniform(n)(old(s)) == (m, s))
      {
        if n != 0 {
          var b := Coin();
          m := if b then 2*m + 1 else 2*m;
          var n := n / 2;
        } else if m < n {
          return m;
        }
      }
    }

    method UniformInterval(a: int, b: int) returns (m: int)
      modifies this
      requires a < b
      ensures Model.UniformInterval(a, b)(old(s)) == (m, s)
      decreases *
    {
      var v := Uniform(b - a);
      assert Model.Uniform(b-a)(old(s)) == (v, s);
      assert Model.UniformInterval(a, b)(old(s)) == (a + v, s);
      m := a + v;
    }

    method {:timeLimit 20} Bernoulli(p: real) returns (c: bool)
      modifies this 
      decreases *
      requires 0.0 <= p <= 1.0
      ensures ProbBernoulliCurried(p, old(s)) == (c, s) 
    {
      c := true;
      var end := false;
      var s' := s;
      var p'': Probability := p as real;
      var p' := p as real;
      assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
      var b := Coin();
      assert (b, s) == Deconstruct(s');
      if b {
        if p'' <= 0.5 {
          c := false;
          end := true;
          assert (end && ProbBernoulliCurried(p, old(s)) == (c, s));
          assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
        } else {
          p'' := 2.0 * (p'' as real) - 1.0;
          calc {
            1.0 >= (p'' as real) >= 0.5;
          ==>
            2.0 >= 2.0 * (p'' as real) >= 1.0;
          ==>
            1.0 >= 2.0 * (p'' as real) - 1.0 >= 0.0;
          }
          assert ProbBernoulliCurried(p', s') == ProbBernoulliCurried(p'', s);
          assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
          assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
          assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s));  
          assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
        }
      } else {
        if p'' <= 0.5 {
          p'' := 2.0 * (p'' as real);
          assert ProbBernoulliCurried(p', s') == ProbBernoulliCurried(p'', s);
          assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
          assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
          assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s));    
        } else {
          c := true;
          end := true;
          assert (end && ProbBernoulliCurried(p, old(s)) == (c, s));
        }
      }

      while true 
        invariant (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s))
        decreases *
      {
        if end {
          assert end && ProbBernoulliCurried(p, old(s)) == (c, s);
          assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
          break;
        } else {
          assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
          s' := s;
          p' := p'';
          b := Coin();
          assert (b, s) == Deconstruct(s');
          if b {
            if p'' <= 0.5 {
              c := false;
              end := true;
              assert ProbBernoulliCurried(p', s') == (c, s);
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
              assert end && ProbBernoulliCurried(p, old(s)) == (c, s);
              assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
            } else {
              calc {
                1.0 >= (p'' as real) >= 0.5;
              ==>
                2.0 >= 2.0 * (p'' as real) >= 1.0;
              ==>
                1.0 >= 2.0 * (p'' as real) - 1.0 >= 0.0;
              }
              p'' := 2.0 * (p'' as real) - 1.0;
              assert ProbBernoulliCurried(p', s') == ProbBernoulliCurried(p'', s);
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
              assert !end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
              assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
            }
          } else {
            if p'' <= 0.5 {
              p'' := 2.0 * (p'' as real);
              assert ProbBernoulliCurried(p', s') == ProbBernoulliCurried(p'', s);
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
              assert !end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s);
              assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
            } else {
              c := true;
              end := true;
              assert ProbBernoulliCurried(p', s') == (c, s);
              assert ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p', s');
              assert end && ProbBernoulliCurried(p, old(s)) == (c, s);
              assert (!end && ProbBernoulliCurried(p, old(s)) == ProbBernoulliCurried(p'', s)) || (end && ProbBernoulliCurried(p, old(s)) == (c, s));
            }
          }
        }
      }

      assert (end && ProbBernoulliCurried(p, old(s)) == (c, s));

    }
  }
}