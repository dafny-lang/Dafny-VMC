/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Monad.dfy"
include "RandomNumberGenerator.dfy"
include "Independence.dfy"
include "Uniform.dfy"
include "MeasureTheory.dfy"

module Bernoulli {
  import opened Monad
  import opened RandomNumberGenerator
  import opened Independence
  import opened Uniform
  import opened MeasureTheory

  /************
   Definitions  
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0
 
  // Equation (4.23)
  function ProbBernoulli(p: Probability): Hurd<bool> {
    assume {:axiom} false;
    var f :=
      (b: bool) =>
        if b then
          if p <= 0.5 then
            Return(false)
          else
            ProbBernoulli(2.0 * p - 1.0)
        else
          if p <= 0.5 then
            ProbBernoulli(2.0 * p)
          else
            Return(true);
    Bind(Deconstruct, f)
  }  

  // Footnote 5, p. 82
  function ProbBernoulliRational(m: nat, n: nat): (f: Hurd<bool>)
    requires n != 0
    requires m <= n
    ensures forall s :: f(s).0 == (ProbUniform(n)(s).0 < m)
    ensures forall s :: f(s).1 == ProbUniform(n)(s).1
  {
    Bind(ProbUniform(n), (k: nat) => Return(k < m))
  }

  /*******
   Lemmas  
  *******/

  lemma ProbBernoulliRationalIsIndepFn(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures IsIndepFn(ProbBernoulliRational(m, n))
  {
    var f := ProbUniform(n);
    var g := (k: nat) => Return(k < m);

    assert IsIndepFn(f) by {
      ProbUniformIsIndepFn(n);
    }

    assert forall k: nat :: IsIndepFn(g(k)) by {
      forall k: nat ensures IsIndepFn(g(k)) {
        ReturnIsIndepFn(k < m);
      }
    }

    IndepFnIsCompositional(f, g);
  }

  lemma {:vcs_split_on_every_assert} BernoulliRationalCorrectness(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var e := iset s | ProbBernoulliRational(m, n)(s).0;
      && e in event_space
      && mu(e) == m as real / n as real
  {
    var e := iset s | ProbBernoulliRational(m, n)(s).0;

    if m == 0 {
      assert e == iset{};
      RNGHasMeasure();
      assert mu(e) == 0.0 by {
        assert IsPositive(event_space, mu);
      }
    } else {
      var e1 := iset s | ProbUniform(n)(s).0 == m-1;
      var e2 := (iset s {:trigger ProbUniform(n)(s).0} | ProbBernoulliRational(m-1, n)(s).0);

      assert (iset s | ProbUniform(n)(s).0 < m-1) == e2 by {
        assert (iset s | ProbUniform(n)(s).0 < m-1) == (iset s {:trigger ProbUniform(n)(s).0} | ProbBernoulliRational(m-1, n)(s).0) by {
          forall s ensures ProbUniform(n)(s).0 < m-1 <==> ProbBernoulliRational(m-1, n)(s).0 {
            assert ProbUniform(n)(s).0 < m-1 <==> ProbBernoulliRational(m-1, n)(s).0;
          }
        }
      }

      calc {
        e;
        iset s | ProbUniform(n)(s).0 < m;
        iset s | ProbUniform(n)(s).0 == m-1 || ProbUniform(n)(s).0 < m-1;
        (iset s | ProbUniform(n)(s).0 == m-1) + (iset s | ProbUniform(n)(s).0 < m-1);
        e1 + e2;
      }
      
      assert e1 in event_space && mu(e1) == 1.0 / (n as real) by {
        UniformFullCorrectness(n, m-1);
      }

      assert e2 in event_space && mu(e2) == (m - 1) as real / n as real by {
        BernoulliRationalCorrectness(m-1, n);
      }

      assume {:axiom} false;

      assert e in event_space by {
        RNGHasMeasure();
        BinaryUnion(event_space, sample_space, e1, e2);
      }

      calc {
        mu(e);
        mu(e1 + e2);
        { assert e1 * e2 == iset{}; }
        mu(e1) + mu(e2);
        (1.0 / (n as real)) + ((m-1) as real / n as real);
        (1.0 + ((m-1) as real)) / n as real;
        (1.0 + (m as real) - 1.0) / n as real;
        m as real / n as real;
      } 
    }
  }

  lemma {:axiom} ProbBernoulliIsIndepFn(p: Probability)
    ensures IsIndepFn(ProbBernoulli(p))

  lemma {:axiom} BernoulliCorrectness(p: Probability)
    ensures 
      var e := iset s | ProbBernoulli(p)(s).0;
      && e in event_space
      && mu(e) == p
}

