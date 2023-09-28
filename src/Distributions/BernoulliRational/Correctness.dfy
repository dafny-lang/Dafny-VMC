/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../Math/MeasureTheory.dfy"
include "../../Math/Helper.dfy"
include "../Uniform/Model.dfy"
include "../Uniform/Correctness.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "Model.dfy"

module BernoulliRationalCorrectness {
  import MeasureTheory
  import Helper
  import UniformModel
  import UniformCorrectness
  import RandomNumberGenerator
  import Independence
  import Monad
  import BernoulliRationalModel

  /*******
   Lemmas
  *******/

  lemma ProbBernoulliRationalIsIndepFn(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures Independence.IsIndepFn(BernoulliRationalModel.ProbBernoulliRational(m, n))
  {
    var f := UniformModel.ProbUniform(n);
    var g := (k: nat) => Monad.Return(k < m);

    assert Independence.IsIndepFn(f) by {
      UniformCorrectness.ProbUniformIsIndepFn(n);
    }

    assert forall k: nat :: Independence.IsIndepFn(g(k)) by {
      forall k: nat ensures Independence.IsIndepFn(g(k)) {
        Independence.ReturnIsIndepFn(k < m);
      }
    }

    Independence.IndepFnIsCompositional(f, g);
  }


  lemma BernoulliRationalCorrectness(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var e := iset s | BernoulliRationalModel.ProbBernoulliRational(m, n)(s).0;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == m as real / n as real
  {
    var e := iset s | BernoulliRationalModel.ProbBernoulliRational(m, n)(s).0;

    if m == 0 {
      assert e == iset{} by {
        forall s ensures !BernoulliRationalModel.ProbBernoulliRational(m, n)(s).0 {
          calc {
            BernoulliRationalModel.ProbBernoulliRational(m, n)(s).0;
            UniformModel.ProbUniform(n)(s).0 < 0;
            false;
          }
        }
      }

      assert e in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e) == 0.0 by {
        RandomNumberGenerator.RNGHasMeasure();
        assert MeasureTheory.IsSigmaAlgebra(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space);
        assert MeasureTheory.IsPositive(RandomNumberGenerator.event_space, RandomNumberGenerator.mu);
      }
    } else {
      var e1 := iset s | UniformModel.ProbUniform(n)(s).0 == m-1;
      var e2 := (iset s {:trigger UniformModel.ProbUniform(n)(s).0} | BernoulliRationalModel.ProbBernoulliRational(m-1, n)(s).0);

      assert (iset s | UniformModel.ProbUniform(n)(s).0 < m-1) == e2 by {
        assert (iset s | UniformModel.ProbUniform(n)(s).0 < m-1) == (iset s {:trigger UniformModel.ProbUniform(n)(s).0} | BernoulliRationalModel.ProbBernoulliRational(m-1, n)(s).0) by {
          forall s ensures UniformModel.ProbUniform(n)(s).0 < m-1 <==> BernoulliRationalModel.ProbBernoulliRational(m-1, n)(s).0 {
            assert UniformModel.ProbUniform(n)(s).0 < m-1 <==> BernoulliRationalModel.ProbBernoulliRational(m-1, n)(s).0;
          }
        }
      }

      calc {
        e;
        iset s | UniformModel.ProbUniform(n)(s).0 < m;
        iset s | UniformModel.ProbUniform(n)(s).0 == m-1 || UniformModel.ProbUniform(n)(s).0 < m-1;
        (iset s | UniformModel.ProbUniform(n)(s).0 == m-1) + (iset s | UniformModel.ProbUniform(n)(s).0 < m-1);
        e1 + e2;
      }

      assert A1: e1 in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e1) == 1.0 / (n as real) by {
        UniformCorrectness.UniformFullCorrectness(n, m-1);
        assert e1 == UniformCorrectness.UniformFullCorrectnessHelper(n, m-1);
      }

      assert A2: e2 in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e2) == (m-1) as real / n as real by {
        BernoulliRationalCorrectness(m-1, n);
      }

      assert A3: (1.0 / n as real) + ((m-1) as real / n as real) == (1.0 + (m-1) as real) / n as real by {
        var x := 1.0;
        var y := (m-1) as real;
        var z := n as real;
        Helper.AdditionOfFractions(x, y, z);
        assert (x / z) + (y / z) == (x + y) / z;
      }

      calc {
        RandomNumberGenerator.mu(e);
        { assert e == e1 + e2; }
        RandomNumberGenerator.mu(e1 + e2);
        { reveal A1; reveal A2; assert e1 * e2 == iset{}; RandomNumberGenerator.RNGHasMeasure(); MeasureTheory.PosCountAddImpliesAdd(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space, RandomNumberGenerator.mu); assert MeasureTheory.IsAdditive(RandomNumberGenerator.event_space, RandomNumberGenerator.mu); }
        RandomNumberGenerator.mu(e1) + RandomNumberGenerator.mu(e2);
        { reveal A1; reveal A2; }
        (1.0 / n as real) + ((m-1) as real / n as real);
        { reveal A3; }
        (1.0 + (m-1) as real) / n as real;
        (1.0 + (m as real) - (1 as real)) / n as real;
        (1.0 + (m as real) - 1.0) / n as real;
        m as real / n as real;
      }

      assert e in RandomNumberGenerator.event_space by {
        RandomNumberGenerator.RNGHasMeasure();
        reveal A1;
        reveal A2;
        MeasureTheory.BinaryUnion(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space, e1, e2);
      }
    }
  }
}