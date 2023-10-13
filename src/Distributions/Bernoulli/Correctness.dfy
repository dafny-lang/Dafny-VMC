/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Bernoulli.Correctness {
  import Measures
  import Helper
  import Uniform
  import Random
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

    Independence.IndepFnIsCompositional(f, g);
  }


  lemma BernoulliCorrectness(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var e := iset s | Model.Sample(m, n)(s).0;
      && e in Random.eventSpace
      && Random.prob(e) == m as real / n as real
  {
    var e := iset s | Model.Sample(m, n)(s).0;

    if m == 0 {
      assert e == iset{} by {
        forall s ensures !Model.Sample(m, n)(s).0 {
          calc {
            Model.Sample(m, n)(s).0;
            Uniform.Model.Sample(n)(s).0 < 0;
            false;
          }
        }
      }

      assert e in Random.eventSpace && Random.prob(e) == 0.0 by {
        Random.ProbIsProbabilityMeasure();
        assert Measures.IsSigmaAlgebra(Random.eventSpace, Random.sampleSpace);
        assert Measures.IsPositive(Random.eventSpace, Random.prob);
      }
    } else {
      var e1 := iset s | Uniform.Model.Sample(n)(s).0 == m-1;
      var e2 := (iset s {:trigger Uniform.Model.Sample(n)(s).0} | Model.Sample(m-1, n)(s).0);

      assert (iset s | Uniform.Model.Sample(n)(s).0 < m-1) == e2 by {
        assert (iset s | Uniform.Model.Sample(n)(s).0 < m-1) == (iset s {:trigger Uniform.Model.Sample(n)(s).0} | Model.Sample(m-1, n)(s).0) by {
          forall s ensures Uniform.Model.Sample(n)(s).0 < m-1 <==> Model.Sample(m-1, n)(s).0 {
            assert Uniform.Model.Sample(n)(s).0 < m-1 <==> Model.Sample(m-1, n)(s).0;
          }
        }
      }

      calc {
        e;
        iset s | Uniform.Model.Sample(n)(s).0 < m;
        iset s | Uniform.Model.Sample(n)(s).0 == m-1 || Uniform.Model.Sample(n)(s).0 < m-1;
        (iset s | Uniform.Model.Sample(n)(s).0 == m-1) + (iset s | Uniform.Model.Sample(n)(s).0 < m-1);
        e1 + e2;
      }

      assert A1: e1 in Random.eventSpace && Random.prob(e1) == 1.0 / (n as real) by {
        Uniform.Correctness.UniformFullCorrectness(n, m-1);
        assert e1 == Uniform.Correctness.SampleEquals(n, m-1);
      }

      assert A2: e2 in Random.eventSpace && Random.prob(e2) == (m-1) as real / n as real by {
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
        Random.prob(e);
        { assert e == e1 + e2; }
        Random.prob(e1 + e2);
        { reveal A1; reveal A2; assert e1 * e2 == iset{}; Random.ProbIsProbabilityMeasure(); Measures.PosCountAddImpliesAdd(Random.eventSpace, Random.sampleSpace, Random.prob); assert Measures.IsAdditive(Random.eventSpace, Random.prob); }
        Random.prob(e1) + Random.prob(e2);
        { reveal A1; reveal A2; }
        (1.0 / n as real) + ((m-1) as real / n as real);
        { reveal A3; }
        (1.0 + (m-1) as real) / n as real;
        (1.0 + (m as real) - (1 as real)) / n as real;
        (1.0 + (m as real) - 1.0) / n as real;
        m as real / n as real;
      }

      assert e in Random.eventSpace by {
        Random.ProbIsProbabilityMeasure();
        reveal A1;
        reveal A2;
        Measures.BinaryUnion(Random.eventSpace, Random.sampleSpace, e1, e2);
      }
    }
  }
}
