/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Correctness {
  import Helper
  import Monad
  import Independence
  import Random
  import Quantifier
  import Loops
  import Measures
  import Model

  /************
   Definitions
  ************/

  ghost predicate UnifIsCorrect(n: nat, k: nat, m: nat)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
  {
    Random.Prob(iset s | Model.Sample(n)(s).0 == m) == if m < Helper.Power(2, k) then 1.0 / (Helper.Power(2, k) as real) else 0.0
  }

  function Sample1(n: nat): Random.Bitstream -> Random.Bitstream
    requires n >= 1
  {
    (s: Random.Bitstream) => Model.Sample(n)(s).1
  }

  /*******
   Lemmas
  *******/

  // Correctness Theorem for Model.Sample.
  // In contrast to UnifCorrectness, this lemma does not follow
  // the thesis, but models PROB_BERN_UNIF of the HOL implementation.
  lemma UnifCorrectness2(n: nat, m: nat)
    requires n >= 1
    ensures
      var e := iset s | Model.Sample(n)(s).0 == m;
      && e in Random.eventSpace
      && Random.Prob(e) == if m < Helper.Power(2, Helper.Log2Floor(n)) then 1.0 / (Helper.Power(2, Helper.Log2Floor(n)) as real) else 0.0
  {
    var e := iset s | Model.Sample(n)(s).0 == m;
    var k := Helper.Log2Floor(n);

    assert e in Random.eventSpace by {
      assert iset{m} in Measures.natEventSpace;
      var preimage := Measures.PreImage((s: Random.Bitstream) => Model.Sample(n)(s).0, iset{m});
      assert preimage in Random.eventSpace by {
        assert Measures.IsMeasurable(Random.eventSpace, Measures.natEventSpace, s => Model.Sample(n)(s).0) by {
          SampleIsIndep(n);
          Independence.IsIndepImpliesFstMeasurableNat(Model.Sample(n));
        }
      }
      assert e == preimage;
    }
    Helper.Power2OfLog2Floor(n);
    UnifCorrectness(n, k);
    assert UnifIsCorrect(n, k, m);
  }

  // See PROB_BERN_UNIF_LT in HOL implementation.
  lemma UnifCorrectness2Inequality(n: nat, m: nat)
    requires n >= 1
    requires m <= Helper.Power(2, Helper.Log2Floor(n))
    ensures
      var e := iset s | Model.Sample(n)(s).0 < m;
      && e in Random.eventSpace
      && Random.Prob(e) == (m as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real)
  {
    var e := iset s | Model.Sample(n)(s).0 < m;

    if m == 0 {
      assert e == iset{};
      Random.ProbIsProbabilityMeasure();
    } else {
      var e1 := iset s | Model.Sample(n)(s).0 < m-1;
      var e2 := iset s | Model.Sample(n)(s).0 == m-1;
      assert e1 in Random.eventSpace by {
        UnifCorrectness2Inequality(n, m-1);
      }
      assert e2 in Random.eventSpace by {
        UnifCorrectness2(n, m-1);
      }
      assert e in Random.eventSpace by {
        assert e == e1 + e2;
        Random.ProbIsProbabilityMeasure();
        Measures.BinaryUnion(Random.eventSpace, Random.sampleSpace, e1, e2);
      }
      calc {
        Random.Prob(e);
        { assert e == e1 + e2; }
        Random.Prob(e1 + e2);
        { assert e1 * e2 == iset{}; Random.ProbIsProbabilityMeasure(); Measures.PosCountAddImpliesAdd(Random.eventSpace, Random.sampleSpace, Random.Prob); assert Measures.IsAdditive(Random.eventSpace, Random.Prob); }
        Random.Prob(e1) + Random.Prob(e2);
        { UnifCorrectness2(n, m-1); UnifCorrectness2Inequality(n, m-1); }
        (1.0 / (Helper.Power(2, Helper.Log2Floor(n)) as real)) + (((m-1) as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real));
        { Helper.AdditionOfFractions(1.0, (m-1) as real, Helper.Power(2, Helper.Log2Floor(n)) as real); }
        (1.0 + (m-1) as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real);
        { assert 1.0 + (m-1) as real == (m as real); }
        (m as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real);
      }
    }
  }

  // Correctness Theorem for Model.Sample.
  // In contrast to UnifCorrectness2, this lemma follows equation (4.8)
  // instead of the HOL implementation.
  lemma UnifCorrectness(n: nat, k: nat)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures forall m: nat :: UnifIsCorrect(n, k, m)
  {
    forall m: nat ensures UnifIsCorrect(n, k, m) {
      assert n >= 1 by { Helper.PowerGreater0(2, k); }
      if k == 0 {
        if m == 0 {
          assert (iset s | Model.Sample(1)(s).0 == m) == (iset s);
        } else {
          assert (iset s | Model.Sample(1)(s).0 == m) == iset{};
        }
        Random.ProbIsProbabilityMeasure();
        assert UnifIsCorrect(n, k, m);
      } else {
        var u := m / 2;
        assert RecursiveCorrect: UnifIsCorrect(n / 2, k - 1, m / 2) by {
          UnifCorrectness(n / 2, k - 1);
        }
        if m < Helper.Power(2, k) {
          calc {
            Random.Prob(iset s | Model.Sample(n)(s).0 == m);
          == { SampleRecursiveHalf(n, m); }
            Random.Prob(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
          == { reveal RecursiveCorrect; }
            (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
          == { Helper.PowerOfTwoLemma(k - 1); }
            1.0 / (Helper.Power(2, k) as real);
          }
          assert UnifIsCorrect(n, k, m);
        } else {
          calc {
            Random.Prob(iset s | Model.Sample(n)(s).0 == m);
          == { SampleRecursiveHalf(n, m); }
            Random.Prob(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
          == { reveal RecursiveCorrect; }
            0.0 / 2.0;
          ==
            0.0;
          }
          assert UnifIsCorrect(n, k, m);
        }
      }
    }
  }

  // Equation (4.7)
  lemma SampleIsIndep(n: nat)
    requires n >= 1
    decreases n
    ensures Independence.IsIndep(Model.Sample(n))
  {
    var fn := Model.Sample(n);
    if n == 1 {
      Independence.ReturnIsIndep(0 as nat);
    } else {
      assert Independence.IsIndep(Model.Sample(n / 2)) by {
        SampleIsIndep(n / 2);
      }
      forall m: nat ensures Independence.IsIndep(Model.UnifStep(m)) {
        Independence.CoinIsIndep();
        var g := Model.UnifStepHelper(m);
        forall b: bool ensures Independence.IsIndep(g(b)) {
          Independence.ReturnIsIndep((if b then 2 * m + 1 else 2 * m) as nat);
        }
        Independence.IndepFnIsCompositional(Monad.Coin, g);
      }
      Independence.IndepFnIsCompositional(Model.Sample(n / 2), Model.UnifStep);
    }
  }

  lemma SampleIsMeasurePreserving(n: nat)
    requires n >= 1
    ensures Measures.IsMeasurePreserving(Random.eventSpace, Random.Prob, Random.eventSpace, Random.Prob, Sample1(n))
  {
    var f := Sample1(n);
    assert Measures.IsMeasurable(Random.eventSpace, Random.eventSpace, f) by {
      SampleIsIndep(n);
      Independence.IsIndepImpliesSndMeasurable(Model.Sample(n));
      assert Independence.IsIndep(Model.Sample(n));
    }
    if n == 1 {
      forall e | e in Random.eventSpace ensures Random.Prob(Measures.PreImage(f, e)) == Random.Prob(e) {
        forall s: Random.Bitstream ensures f(s) == s {
          assert f(s) == s;
        }
        Measures.PreImageIdentity(f, e);
      }
      assert Measures.IsMeasurePreserving(Random.eventSpace, Random.Prob, Random.eventSpace, Random.Prob, f);
    } else {
      var g := Sample1(n / 2);
      forall e | e in Random.eventSpace ensures Random.Prob(Measures.PreImage(f, e)) == Random.Prob(e) {
        var e' := (iset s | Monad.Tail(s) in e);
        assert e' in Random.eventSpace by {
          assert e' == Measures.PreImage(Monad.Tail, e);
          Monad.TailIsMeasurePreserving();
          assert Measures.IsMeasurable(Random.eventSpace, Random.eventSpace, Monad.Tail);
        }
        assert Measures.PreImage(f, e) == Measures.PreImage(g, e') by {
          assert forall s :: f(s) in e <==> g(s) in e' by {
            forall s ensures f(s) in e <==> g(s) in e' {
              calc {
                f(s) in e;
              <==> { assert f(s) == Model.Sample(n)(s).1; }
                Model.Sample(n)(s).1 in e;
              <==> { SampleTailDecompose(n, s); }
                Monad.Tail(Model.Sample(n / 2)(s).1) in e;
              <==>
                Model.Sample(n / 2)(s).1 in e';
              <==> { assert Model.Sample(n / 2)(s).1 == g(s); }
                g(s) in e';
              }
            }
          }
          Measures.PreImagesEqual(f, e, g, e');
        }
        assert Random.Prob(Measures.PreImage(f, e)) == Random.Prob(e) by {
          calc {
            Random.Prob(Measures.PreImage(f, e));
          ==
            Random.Prob(Measures.PreImage(g, e'));
          == { SampleIsMeasurePreserving(n / 2); assert Measures.IsMeasurePreserving(Random.eventSpace, Random.Prob, Random.eventSpace, Random.Prob, g); assert e' in Random.eventSpace; }
            Random.Prob(e');
          == { assert e' == Measures.PreImage(Monad.Tail, e); }
            Random.Prob(Measures.PreImage(Monad.Tail, e));
          == { Monad.TailIsMeasurePreserving(); }
            Random.Prob(e);
          }
        }
      }
      assert Measures.IsMeasurePreserving(Random.eventSpace, Random.Prob, Random.eventSpace, Random.Prob, f);
    }
  }

  lemma SampleTailDecompose(n: nat, s: Random.Bitstream)
    requires n >= 2
    ensures Model.Sample(n)(s).1 == Monad.Tail(Model.Sample(n / 2)(s).1)
  {
    var (a, s') := Model.Sample(n / 2)(s);
    var (b, s'') := Monad.Coin(s');
    calc {
      Model.Sample(n)(s).1;
    ==
      Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).1;
    ==
      Model.UnifStep(a)(s').1;
    ==
      Monad.Bind(Monad.Coin, (b: bool) => Monad.Return((if b then 2*a + 1 else 2*a) as nat))(s').1;
    ==
      Monad.Return((if b then 2*a + 1 else 2*a) as nat)(s'').1;
    ==
      s'';
    ==
      Monad.Tail(s');
    ==
      Monad.Tail(Model.Sample(n / 2)(s).1);
    }
  }

  lemma SampleSetEquality(n: nat, m: nat)
    requires n >= 2
    ensures
      var b_of := (s: Random.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).1).0;
      var a_of := (s: Random.Bitstream) => Model.Sample(n / 2)(s).0;
      (iset s | Model.Sample(n)(s).0 == m) == (iset s | 2*a_of(s) + Helper.boolToNat(b_of(s)) == m)
  {
    var b_of := (s: Random.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).1).0;
    var a_of := (s: Random.Bitstream) => Model.Sample(n / 2)(s).0;
    forall s ensures Model.Sample(n)(s).0 == m <==> (2 * a_of(s) + Helper.boolToNat(b_of(s)) == m) {
      var (a, s') := Model.Sample(n / 2)(s);
      var (b, s'') := Monad.Coin(s');
      calc {
        Model.Sample(n)(s).0;
      ==
        Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).0;
      ==
        Model.UnifStep(a)(s').0;
      ==
        Monad.Bind(Monad.Coin, b => Monad.Return((if b then 2*a + 1 else 2*a) as nat))(s').0;
      ==
        Monad.Return((if b then 2*a + 1 else 2*a) as nat)(s'').0;
      ==
        if b then 2*a + 1 else 2*a;
      }
    }
  }

  lemma SampleRecursiveHalf(n: nat, m: nat)
    requires n >= 2
    ensures Random.Prob(iset s | Model.Sample(n)(s).0 == m) == Random.Prob(iset s | Model.Sample(n / 2)(s).0 == m / 2) / 2.0
  {
    var a_of: Random.Bitstream -> nat := (s: Random.Bitstream) => Model.Sample(n / 2)(s).0;
    var b_of: Random.Bitstream -> bool := (s: Random.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).1).0;
    var A: iset<nat> := (iset x: nat | x == m / 2);
    var E: iset<Random.Bitstream> := (iset s | m % 2 as nat == Helper.boolToNat(Monad.Coin(s).0));
    var f := (s: Random.Bitstream) => Model.Sample(n / 2)(s).1;

    var e1 := (iset s | Model.Sample(n / 2)(s).1 in E);
    var e2 := (iset s | Model.Sample(n / 2)(s).0 in A);
    var e3 := (iset s | 2*a_of(s) + Helper.boolToNat(b_of(s)) == m);

    assert SplitEvent: e3 == e1 * e2 by {
      forall s ensures s in e3 <==> s in e1 && s in e2 {
        var a: nat := a_of(s);
        var b: nat := Helper.boolToNat(b_of(s));
        assert b < 2;
        calc {
          s in e3;
          2 * a + b == m;
          m == a * 2 + b;
          (a == m / 2) && (b == m % 2);
          s in e1 && s in e2;
        }
      }
    }

    assert Eq2: (iset s | a_of(s) == m / 2) == e2 by {
      forall s ensures a_of(s) == m / 2 <==> Model.Sample(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | a_of(s) == m / 2) == (iset s | Model.Sample(n / 2)(s).0 == m / 2) by {
      forall s ensures a_of(s) == m / 2 <==> Model.Sample(n / 2)(s).0 == m / 2 {
        assert a_of(s) == Model.Sample(n / 2)(s).0;
      }
    }

    assert Eq4: e1 == Measures.PreImage(f, E) by {
      forall s ensures Model.Sample(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert E in Random.eventSpace && Random.Prob(E) == 0.5 by {
      assert E == (iset s | Monad.Head(s) == (m % 2 == 1));
      Monad.CoinHasProbOneHalf(m % 2 == 1);
    }

    assert Indep: Random.Prob(e1 * e2) == Random.Prob(e1) * Random.Prob(e2) by {
      assert Measures.AreIndepEvents(Random.eventSpace, Random.Prob, e1, e2) by {
        assert Independence.IsIndepFunction(Model.Sample(n / 2)) by {
          assert Independence.IsIndep(Model.Sample(n / 2)) by {
            SampleIsIndep(n / 2);
          }
          Independence.IsIndepImpliesIsIndepFunction(Model.Sample(n / 2));
        }
        assert E in Random.eventSpace;
        assert Independence.IsIndepFunctionCondition(Model.Sample(n / 2), A, E);
      }
      Independence.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert ProbE1: Random.Prob(e1) == 0.5 by {
      calc {
        0.5;
      ==
        Random.Prob(E);
      == { SampleIsMeasurePreserving(n / 2); }
        Random.Prob(Measures.PreImage(f, E));
      == { reveal Eq4; }
        Random.Prob(e1);
      }
    }

    calc {
      Random.Prob(iset s | Model.Sample(n)(s).0 == m);
    == { SampleSetEquality(n, m); }
      Random.Prob(e3);
    == { reveal SplitEvent; }
      Random.Prob(e1 * e2);
    == { reveal Indep; }
      Random.Prob(e1) * Random.Prob(e2);
    == { reveal ProbE1; Helper.Congruence(Random.Prob(e1), 0.5, x => x * Random.Prob(e2)); }
      0.5 * Random.Prob(e2);
    ==
      Random.Prob(e2) / 2.0;
    == { reveal Eq2; }
      Random.Prob(iset s | a_of(s) == m / 2) / 2.0;
    == { reveal Eq3; }
      Random.Prob(iset s | Model.Sample(n / 2)(s).0 == m / 2) / 2.0;
    }
  }
}
