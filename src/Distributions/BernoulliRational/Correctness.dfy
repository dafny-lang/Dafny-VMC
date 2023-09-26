/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../Math/Helper.dfy"
include "../Uniform/Model.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "Model.dfy"

import opened MeasureTheory
import opened Helper
import opened Independence
import opened BernoulliRationalModel
import opened RandomNumberGenerator
import opened UniformModel

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


lemma {:timeLimit 20} {:vcs_split_on_every_assert} BernoulliRationalCorrectness(m: nat, n: nat)
  requires n != 0
  requires m <= n
  ensures
    var e := iset s | ProbBernoulliRational(m, n)(s).0;
    && e in event_space
    && mu(e) == m as real / n as real
{
  var e := iset s | ProbBernoulliRational(m, n)(s).0;

  if m == 0 {
    assert e == iset{} by {
      forall s ensures !ProbBernoulliRational(m, n)(s).0 {
        calc {
          ProbBernoulliRational(m, n)(s).0;
          ProbUniform(n)(s).0 < 0;
          false;
        }
      }
    }

    assert e in event_space && mu(e) == 0.0 by {
      RNGHasMeasure();
      assert IsSigmaAlgebra(event_space, sample_space);
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

    assert A1: e1 in event_space && mu(e1) == 1.0 / (n as real) by {
      UniformFullCorrectness(n, m-1);
    }

    assert A2: e2 in event_space && mu(e2) == (m-1) as real / n as real by {
      BernoulliRationalCorrectness(m-1, n);
    }

    assert A3: (1.0 / n as real) + ((m-1) as real / n as real) == (1.0 + (m-1) as real) / n as real by {
      var x := 1.0;
      var y := (m-1) as real;
      var z := n as real;
      AdditionOfFractions(x, y, z);
      assert (x / z) + (y / z) == (x + y) / z;
    }

    calc {
      mu(e);
      { assert e == e1 + e2; }
      mu(e1 + e2);
      { reveal A1; reveal A2; assert e1 * e2 == iset{}; RNGHasMeasure(); LemmaPosCountAddImpliesAdd(event_space, sample_space, mu); assert IsAdditive(event_space, mu); }
      mu(e1) + mu(e2);
      { reveal A1; reveal A2; }
      (1.0 / n as real) + ((m-1) as real / n as real);
      { reveal A3; }
      (1.0 + (m-1) as real) / n as real;
      (1.0 + (m as real) - (1 as real)) / n as real;
      (1.0 + (m as real) - 1.0) / n as real;
      m as real / n as real;
    }

    assert e in event_space by {
      RNGHasMeasure();
      reveal A1;
      reveal A2;
      BinaryUnion(event_space, sample_space, e1, e2);
    }
  }
}