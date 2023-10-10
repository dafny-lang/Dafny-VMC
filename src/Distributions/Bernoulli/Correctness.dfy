/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Correctness {
  import Partials
  import MeasureTheory
  import Helper
  import Uniform
  import RandomNumberGenerator
  import Independence
  import Monad
  import Model

  /*******
   Lemmas
  *******/

  lemma SampleIsIndepFn(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures Independence.IsIndepFn(Model.Sample(m, n))
  {
    var f := Uniform.Model.Sample(n);
    var g := (k: nat) => Monad.Return(k < m);

    assert Independence.IsIndepFn(f) by {
      Uniform.Correctness.SampleIsIndepFn(n);
    }

    assert forall k: nat :: Independence.IsIndepFn(g(k)) by {
      forall k: nat ensures Independence.IsIndepFn(g(k)) {
        Independence.ReturnIsIndepFn(k < m);
      }
    }

    Independence.IndepFnIsCompositionalPartial(f, g);
  }


  lemma BernoulliCorrectness(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var e := iset s | Model.Sample(m, n)(s).Value() == Partials.Terminating(true);
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == m as real / n as real
  {
    var e := iset s | Model.Sample(m, n)(s).Value() == Partials.Terminating(true);

    if m == 0 {
      assert e == iset{} by {
        forall s ensures Model.Sample(m, n)(s).Value() == Partials.Terminating(false) {
          calc {
            Model.Sample(m, n)(s).Value();
            Uniform.Model.Sample(n)(s).Value().Map(v => v < 0);
            Partials.Terminating(false);
          }
        }
      }

      assert e in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e) == 0.0 by {
        RandomNumberGenerator.RNGHasMeasure();
        assert MeasureTheory.IsSigmaAlgebra(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space);
        assert MeasureTheory.IsPositive(RandomNumberGenerator.event_space, RandomNumberGenerator.mu);
      }
    } else {
      var e1 := iset s | Uniform.Model.Sample(n)(s).Value() == Partials.Terminating(m-1);
      var e2 := (iset s {:trigger Uniform.Model.Sample(n)(s)} | Model.Sample(m-1, n)(s).ValueSatisfies(v => v));

      assert (iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1)) == e2 by {
        assert (iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1)) == (iset s {:trigger Uniform.Model.Sample(n)(s)} | Model.Sample(m-1, n)(s).Value() == Partials.Terminating(true)) by {
          forall s ensures Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1) <==> Model.Sample(m-1, n)(s).ValueSatisfies(x => x) {
            assert Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1) <==> Model.Sample(m-1, n)(s).ValueSatisfies(x => x);
          }
        }
      }

      calc {
        e;
        iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m);
        iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x == m-1) || Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1);
        (iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x == m-1)) + (iset s | Uniform.Model.Sample(n)(s).ValueSatisfies(x => x < m-1));
        e1 + e2;
      }

      assert A1: e1 in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e1) == 1.0 / (n as real) by {
        Uniform.Correctness.UniformFullCorrectness(n, m-1);
        assert e1 == Uniform.Correctness.SampleEquals(n, m-1);
      }

      assert A2: e2 in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(e2) == (m-1) as real / n as real by {
        BernoulliCorrectness(m-1, n);
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
