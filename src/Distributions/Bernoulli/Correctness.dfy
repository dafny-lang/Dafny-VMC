/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Correctness {
  import Measures
  import Helper
  import Uniform
  import Rand
  import Independence
  import Monad
  import Model

  /*******
   Lemmas
  *******/

  lemma SampleIsIndep(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures Independence.IsIndep(Model.Sample(m, n))
  {
    var f := Uniform.Model.Sample(n);
    var g := (k: nat) => Monad.Return(k < m);

    assert Independence.IsIndep(f) by {
      Uniform.Correctness.SampleIsIndep(n);
    }

    assert forall k: nat :: Independence.IsIndep(g(k)) by {
      forall k: nat ensures Independence.IsIndep(g(k)) {
        Independence.ReturnIsIndep(k < m);
      }
    }

    Independence.BindIsIndep(f, g);
    reveal Model.Sample();
  }


  lemma BernoulliCorrectness(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var e := iset s | Model.Sample(m, n)(s).value;
      && e in Rand.eventSpace
      && Rand.prob(e) == m as real / n as real
  {
    var e := iset s | Model.Sample(m, n)(s).value;

    if m == 0 {
      assert e == iset{} by {
        forall s ensures !Model.Sample(m, n)(s).value {
          calc {
            Model.Sample(m, n)(s).value;
            Uniform.Model.Sample(n)(s).value < 0;
            false;
          }
        }
      }

      assert e in Rand.eventSpace && Rand.prob(e) == 0.0 by {
        Rand.ProbIsProbabilityMeasure();
        assert Measures.IsSigmaAlgebra(Rand.eventSpace, Rand.sampleSpace);
        assert Measures.IsPositive(Rand.eventSpace, Rand.prob);
      }
    } else {
      var e1 := iset s | Uniform.Model.Sample(n)(s).value == m-1;
      var e2 := (iset s {:trigger Uniform.Model.Sample(n)(s).value} | Model.Sample(m-1, n)(s).value);

      assert (iset s | Uniform.Model.Sample(n)(s).value < m-1) == e2 by {
        assert (iset s | Uniform.Model.Sample(n)(s).value < m-1) == (iset s {:trigger Uniform.Model.Sample(n)(s).value} | Model.Sample(m-1, n)(s).value) by {
          forall s ensures Uniform.Model.Sample(n)(s).value < m-1 <==> Model.Sample(m-1, n)(s).value {
            assert Uniform.Model.Sample(n)(s).value < m-1 <==> Model.Sample(m-1, n)(s).value;
          }
        }
      }

      assert e == e1 + e2 by {
        calc {
          e;
          iset s | Uniform.Model.Sample(n)(s).value < m;
          iset s | Uniform.Model.Sample(n)(s).value == m-1 || Uniform.Model.Sample(n)(s).value < m-1;
          (iset s | Uniform.Model.Sample(n)(s).value == m-1) + (iset s | Uniform.Model.Sample(n)(s).value < m-1);
          e1 + e2;
        }
      }

      assert A1: e1 in Rand.eventSpace && Rand.prob(e1) == 1.0 / (n as real) by {
        Uniform.Correctness.UniformFullCorrectness(n, m-1);
        assert e1 == Uniform.Correctness.SampleEquals(n, m-1);
      }

      assert A2: e2 in Rand.eventSpace && Rand.prob(e2) == (m-1) as real / n as real by {
        BernoulliCorrectness(m-1, n);
      }

      calc {
        Rand.prob(e);
        Rand.prob(e1 + e2);
        { reveal A1; reveal A2; assert e1 * e2 == iset{}; Rand.ProbIsProbabilityMeasure(); Measures.PosCountAddImpliesAdd(Rand.eventSpace, Rand.sampleSpace, Rand.prob); assert Measures.IsAdditive(Rand.eventSpace, Rand.prob); }
        Rand.prob(e1) + Rand.prob(e2);
        { reveal A1; reveal A2; }
        (1.0 / n as real) + ((m - 1) as real / n as real);
        { AdditionOfFractions(m, n); }
        m as real / n as real;
      }

      assert e in Rand.eventSpace by {
        Rand.ProbIsProbabilityMeasure();
        reveal A1;
        reveal A2;
        Measures.BinaryUnion(Rand.eventSpace, Rand.sampleSpace, e1, e2);
      }
    }
  }

  lemma AdditionOfFractions(m: nat, n: nat)
    requires n > 0
    ensures (1.0 / n as real) + ((m - 1) as real / n as real) == (m as real) / n as real
  {}
}
