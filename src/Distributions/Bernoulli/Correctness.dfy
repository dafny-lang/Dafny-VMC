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
    var g := (k: nat) => k < m;

    assert Independence.IsIndep(f) by {
      Uniform.Correctness.SampleIsIndep(n);
    }

    Independence.MapIsIndep(f, g);
    reveal Model.Sample();
  }

  // The probability mass function (PMF) of the bernoulli distribution
  function BernoulliMass(numer: nat, denom: nat): bool -> real
    requires denom > 0
    requires numer <= denom
  {
    b => if b then numer as real / denom as real else 1.0 - numer as real / denom as real
  }

  lemma BernoulliCorrectness(m: nat, n: nat, b: bool)
    requires n != 0
    requires m <= n
    ensures
      var event := iset s | Model.Sample(m, n)(s).Equals(b);
      && event in Rand.eventSpace
      && Rand.prob(event) == BernoulliMass(m, n)(b)
  {
    if b {
      BernoulliCorrectnessCaseTrue(m, n);
    } else {
      BernoulliCorrectnessCaseFalse(m, n);
    }
  }

  lemma {:axiom} BernoulliCorrectnessCaseFalse(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var falseEvent := iset s | Model.Sample(m, n)(s).Equals(false);
      && falseEvent in Rand.eventSpace
      && Rand.prob(falseEvent) == 1.0 - m as real / n as real


  lemma BernoulliCorrectnessCaseTrue(m: nat, n: nat)
    requires n != 0
    requires m <= n
    ensures
      var trueEvent := iset s | Model.Sample(m, n)(s).Equals(true);
      && trueEvent in Rand.eventSpace
      && Rand.prob(trueEvent) == m as real / n as real
  {
    reveal Model.Sample();
    var e := iset s | Model.Sample(m, n)(s).Equals(true);
    var ltM: nat -> bool := x => x < m;
    var ltM1: nat -> bool := x => x < m - 1;

    if m == 0 {
      assert e == iset{} by {
        forall s ensures !Model.Sample(m, n)(s).Equals(true) {
          calc {
            Model.Sample(m, n)(s).Equals(true);
            Uniform.Model.Sample(n)(s).Satisfies(x => x < 0);
            false;
          }
        }
      }

      assert e in Rand.eventSpace && Rand.prob(e) == 0.0 by {
        Rand.ProbIsProbabilityMeasure();
        assert Measures.IsSigmaAlgebra(Rand.eventSpace);
        assert Measures.IsPositive(Rand.eventSpace, Rand.prob);
      }
    } else {
      var e1 := iset s | Uniform.Model.Sample(n)(s).Equals(m - 1);
      var e2 := (iset s {:trigger Uniform.Model.Sample(n)(s).value} | Model.Sample(m-1, n)(s).Equals(true));

      assert (iset s | Uniform.Model.Sample(n)(s).Satisfies(ltM1)) == e2 by {
        assert (iset s | Uniform.Model.Sample(n)(s).Satisfies(ltM1)) == (iset s {:trigger Uniform.Model.Sample(n)(s).value} | Model.Sample(m-1, n)(s).Equals(true)) by {
          forall s ensures Uniform.Model.Sample(n)(s).Satisfies(ltM1) <==> Model.Sample(m-1, n)(s).Equals(true) {
            assert Uniform.Model.Sample(n)(s).Satisfies(ltM1) <==> Model.Sample(m-1, n)(s).Equals(true);
          }
        }
      }

      assert e == e1 + e2 by {
        calc {
          e;
          iset s | Uniform.Model.Sample(n)(s).Satisfies(ltM);
          iset s | Uniform.Model.Sample(n)(s).Equals(m-1) || Uniform.Model.Sample(n)(s).Satisfies(ltM1);
          (iset s | Uniform.Model.Sample(n)(s).Equals(m-1)) + (iset s | Uniform.Model.Sample(n)(s).Satisfies(ltM1));
          e1 + e2;
        }
      }

      assert A1: e1 in Rand.eventSpace && Rand.prob(e1) == 1.0 / (n as real) by {
        Uniform.Correctness.UniformFullCorrectness(n, m-1);
        assert e1 == Uniform.Correctness.SampleEquals(n, m-1);
      }

      assert A2: e2 in Rand.eventSpace && Rand.prob(e2) == (m-1) as real / n as real by {
        BernoulliCorrectnessCaseTrue(m-1, n);
      }

      calc {
        Rand.prob(e);
        Rand.prob(e1 + e2);
        { reveal A1; reveal A2; assert e1 * e2 == iset{}; Rand.ProbIsProbabilityMeasure(); Measures.PosCountAddImpliesAdd(Rand.eventSpace, Rand.prob); assert Measures.IsAdditive(Rand.eventSpace, Rand.prob); }
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
        Measures.BinaryUnionIsMeasurable(Rand.eventSpace, e1, e2);
      }
    }
  }

  lemma AdditionOfFractions(m: nat, n: nat)
    requires n > 0
    ensures (1.0 / n as real) + ((m - 1) as real / n as real) == (m as real) / n as real
  {}
}
