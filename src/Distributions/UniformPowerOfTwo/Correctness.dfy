/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Correctness {
  import Helper
  import Monad
  import Rand
  import Quantifier
  import Measures
  import Model

  /************
   Definitions
  ************/

  ghost predicate UnifIsCorrect(n: nat, k: nat, m: nat)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
  {
    Rand.prob(iset s | Model.Sample(n)(s).value == m) == if m < Helper.Power(2, k) then 1.0 / (Helper.Power(2, k) as real) else 0.0
  }

  function SampleRest(n: nat): Rand.Bitstream -> Rand.Bitstream
    requires n >= 1
  {
    (s: Rand.Bitstream) => Model.Sample(n)(s).rest
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
      var e := iset s | Model.Sample(n)(s).value == m;
      && e in Rand.eventSpace
      && Rand.prob(e) == if m < Helper.Power(2, Helper.Log2Floor(n)) then 1.0 / (Helper.Power(2, Helper.Log2Floor(n)) as real) else 0.0
  {
    var e := iset s | Model.Sample(n)(s).value == m;
    var k := Helper.Log2Floor(n);

    assert e in Rand.eventSpace by {
      var resultsWithValueM := Monad.ResultsWithValueIn(iset{m});
      assert resultsWithValueM in Monad.natResultEventSpace by {
        Monad.LiftInEventSpaceToResultEventSpace(iset{m}, Measures.natEventSpace);
      }
      var preimage := Measures.PreImage(Model.Sample(n), resultsWithValueM);
      assert Measures.IsMeasurable(Rand.eventSpace, Monad.natResultEventSpace, Model.Sample(n)) by {
        SampleIsIndep(n);
        Monad.IsIndepImpliesMeasurableNat(Model.Sample(n));
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
      var e := iset s | Model.Sample(n)(s).value < m;
      && e in Rand.eventSpace
      && Rand.prob(e) == (m as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real)
  {
    var e := iset s | Model.Sample(n)(s).value < m;

    if m == 0 {
      assert e == iset{};
      Rand.ProbIsProbabilityMeasure();
    } else {
      var e1 := iset s | Model.Sample(n)(s).value < m-1;
      var e2 := iset s | Model.Sample(n)(s).value == m-1;
      assert e1 in Rand.eventSpace by {
        UnifCorrectness2Inequality(n, m-1);
      }
      assert e2 in Rand.eventSpace by {
        UnifCorrectness2(n, m-1);
      }
      assert e in Rand.eventSpace by {
        assert e == e1 + e2;
        Rand.ProbIsProbabilityMeasure();
        Measures.BinaryUnion(Rand.eventSpace, Rand.sampleSpace, e1, e2);
      }
      calc {
        Rand.prob(e);
        { assert e == e1 + e2; }
        Rand.prob(e1 + e2);
        { assert e1 * e2 == iset{}; Rand.ProbIsProbabilityMeasure(); Measures.PosCountAddImpliesAdd(Rand.eventSpace, Rand.sampleSpace, Rand.prob); assert Measures.IsAdditive(Rand.eventSpace, Rand.prob); }
        Rand.prob(e1) + Rand.prob(e2);
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
        reveal Model.Sample();
        if m == 0 {
          assert (iset s | Model.Sample(1)(s).value == m) == (iset s);
        } else {
          assert (iset s | Model.Sample(1)(s).value == m) == iset{};
        }
        Rand.ProbIsProbabilityMeasure();
        assert UnifIsCorrect(n, k, m);
      } else {
        var u := m / 2;
        assert RecursiveCorrect: UnifIsCorrect(n / 2, k - 1, m / 2) by {
          UnifCorrectness(n / 2, k - 1);
        }
        if m < Helper.Power(2, k) {
          calc {
            Rand.prob(iset s | Model.Sample(n)(s).value == m);
          == { SampleRecursiveHalf(n, m); }
            Rand.prob(iset s | Model.Sample(n / 2)(s).value == u) / 2.0;
          == { reveal RecursiveCorrect; }
            (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
          == { Helper.PowerOfTwoLemma(k - 1); }
            1.0 / (Helper.Power(2, k) as real);
          }
          assert UnifIsCorrect(n, k, m);
        } else {
          calc {
            Rand.prob(iset s | Model.Sample(n)(s).value == m);
          == { SampleRecursiveHalf(n, m); }
            Rand.prob(iset s | Model.Sample(n / 2)(s).value == u) / 2.0;
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
    ensures Monad.IsIndep(Model.Sample(n))
  {
    var fn := Model.Sample(n);
    reveal Model.Sample();
    if n == 1 {
      Monad.ReturnIsIndep(0 as nat);
    } else {
      assert Monad.IsIndep(Model.Sample(n / 2)) by {
        SampleIsIndep(n / 2);
      }
      forall m: nat ensures Monad.IsIndep(Model.UnifStep(m)) {
        Monad.CoinIsIndep();
        var g := Model.UnifStepHelper(m);
        forall b: bool ensures Monad.IsIndep(g(b)) {
          Monad.ReturnIsIndep((if b then 2 * m + 1 else 2 * m) as nat);
        }
        Monad.BindIsIndep(Monad.Coin, g);
      }
      Monad.BindIsIndep(Model.Sample(n / 2), Model.UnifStep);
    }
  }

  lemma SampleIsMeasurePreserving(n: nat)
    requires n >= 1
    ensures Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, SampleRest(n))
  {
    var f := SampleRest(n);
    assert Measures.IsMeasurable(Rand.eventSpace, Rand.eventSpace, f) by {
      forall e | e in Rand.eventSpace ensures Measures.PreImage(f, e) in Rand.eventSpace {
        var resultsWithRestInE := Monad.ResultsWithRestIn(e);
        assert resultsWithRestInE in Monad.natResultEventSpace by {
          Monad.LiftRestInEventSpaceToResultEventSpace(e, Measures.natEventSpace);
        }
        var preimage' := Measures.PreImage(Model.Sample(n), resultsWithRestInE);
        assert preimage' in Rand.eventSpace by {
          SampleIsIndep(n);
          Monad.IsIndepImpliesMeasurableNat(Model.Sample(n));
        }
        assert Measures.PreImage(f, e) == preimage';
      }
    }
    if n == 1 {
      forall e | e in Rand.eventSpace ensures Rand.prob(Measures.PreImage(f, e)) == Rand.prob(e) {
        forall s: Rand.Bitstream ensures f(s) == s {
          reveal Model.Sample();
          assert f(s) == s;
        }
        Measures.PreImageIdentity(f, e);
      }
      assert Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, f);
    } else {
      var g := SampleRest(n / 2);
      forall e | e in Rand.eventSpace ensures Rand.prob(Measures.PreImage(f, e)) == Rand.prob(e) {
        var e' := (iset s | Rand.Tail(s) in e);
        assert e' in Rand.eventSpace by {
          assert e' == Measures.PreImage(Rand.Tail, e);
          Rand.TailIsMeasurePreserving();
          assert Measures.IsMeasurable(Rand.eventSpace, Rand.eventSpace, Rand.Tail);
        }
        assert Measures.PreImage(f, e) == Measures.PreImage(g, e') by {
          assert forall s :: f(s) in e <==> g(s) in e' by {
            forall s ensures f(s) in e <==> g(s) in e' {
              calc {
                f(s) in e;
              <==> { assert f(s) == Model.Sample(n)(s).rest; }
                Model.Sample(n)(s).rest in e;
              <==> { SampleTailDecompose(n, s); }
                Rand.Tail(Model.Sample(n / 2)(s).rest) in e;
              <==>
                Model.Sample(n / 2)(s).rest in e';
              <==> { assert Model.Sample(n / 2)(s).rest == g(s); }
                g(s) in e';
              }
            }
          }
          Measures.PreImagesEqual(f, e, g, e');
        }
        assert Rand.prob(Measures.PreImage(f, e)) == Rand.prob(e) by {
          calc {
            Rand.prob(Measures.PreImage(f, e));
          ==
            Rand.prob(Measures.PreImage(g, e'));
          == { SampleIsMeasurePreserving(n / 2); assert Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, g); assert e' in Rand.eventSpace; }
            Rand.prob(e');
          == { assert e' == Measures.PreImage(Rand.Tail, e); }
            Rand.prob(Measures.PreImage(Rand.Tail, e));
          == { Rand.TailIsMeasurePreserving(); }
            Rand.prob(e);
          }
        }
      }
      assert Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, f);
    }
  }

  lemma SampleTailDecompose(n: nat, s: Rand.Bitstream)
    requires n >= 2
    ensures Model.Sample(n)(s).rest == Rand.Tail(Model.Sample(n / 2)(s).rest)
  {
    var Result(a, s') := Model.Sample(n / 2)(s);
    var Result(b, s'') := Monad.Coin(s');
    calc {
      Model.Sample(n)(s).rest;
    == { reveal Model.Sample(); }
      Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).rest;
    ==
      Model.UnifStep(a)(s').rest;
    ==
      Monad.Bind(Monad.Coin, (b: bool) => Monad.Return((if b then 2*a + 1 else 2*a) as nat))(s').rest;
    ==
      Monad.Return((if b then 2*a + 1 else 2*a) as nat)(s'').rest;
    ==
      s'';
    ==
      Rand.Tail(s');
    ==
      Rand.Tail(Model.Sample(n / 2)(s).rest);
    }
  }

  lemma SampleSetEquality(n: nat, m: nat)
    requires n >= 2
    ensures
      var bOf := (s: Rand.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).rest).value;
      var aOf := (s: Rand.Bitstream) => Model.Sample(n / 2)(s).value;
      (iset s | Model.Sample(n)(s).value == m) == (iset s | 2*aOf(s) + Helper.boolToNat(bOf(s)) == m)
  {
    var bOf := (s: Rand.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).rest).value;
    var aOf := (s: Rand.Bitstream) => Model.Sample(n / 2)(s).value;
    forall s ensures Model.Sample(n)(s).value == m <==> (2 * aOf(s) + Helper.boolToNat(bOf(s)) == m) {
      var Result(a, s') := Model.Sample(n / 2)(s);
      var Result(b, s'') := Monad.Coin(s');
      calc {
        Model.Sample(n)(s).value;
      == { reveal Model.Sample(); }
        Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).value;
      ==
        Model.UnifStep(a)(s').value;
      ==
        Monad.Bind(Monad.Coin, b => Monad.Return((if b then 2*a + 1 else 2*a) as nat))(s').value;
      ==
        Monad.Return((if b then 2*a + 1 else 2*a) as nat)(s'').value;
      ==
        if b then 2*a + 1 else 2*a;
      }
    }
  }

  lemma SampleRecursiveHalf(n: nat, m: nat)
    requires n >= 2
    ensures Rand.prob(iset s | Model.Sample(n)(s).value == m) == Rand.prob(iset s | Model.Sample(n / 2)(s).value == m / 2) / 2.0
  {
    var aOf: Rand.Bitstream -> nat := (s: Rand.Bitstream) => Model.Sample(n / 2)(s).value;
    var bOf: Rand.Bitstream -> bool := (s: Rand.Bitstream) => Monad.Coin(Model.Sample(n / 2)(s).rest).value;
    var A: iset<nat> := (iset x: nat | x == m / 2);
    var E: iset<Rand.Bitstream> := (iset s | m % 2 as nat == Helper.boolToNat(Monad.Coin(s).value));
    var f := (s: Rand.Bitstream) => Model.Sample(n / 2)(s).rest;

    var e1 := (iset s | Model.Sample(n / 2)(s).RestIn(E));
    var e2 := (iset s | Model.Sample(n / 2)(s).In(A));
    var e3 := (iset s | 2*aOf(s) + Helper.boolToNat(bOf(s)) == m);

    assert SplitEvent: e3 == e1 * e2 by {
      forall s ensures s in e3 <==> s in e1 && s in e2 {
        var a: nat := aOf(s);
        var b: nat := Helper.boolToNat(bOf(s));
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

    assert Eq2: (iset s | aOf(s) == m / 2) == e2 by {
      forall s ensures aOf(s) == m / 2 <==> Model.Sample(n / 2)(s).value in A {
      }
    }

    assert Eq3: (iset s | aOf(s) == m / 2) == (iset s | Model.Sample(n / 2)(s).value == m / 2) by {
      forall s ensures aOf(s) == m / 2 <==> Model.Sample(n / 2)(s).value == m / 2 {
        assert aOf(s) == Model.Sample(n / 2)(s).value;
      }
    }

    assert Eq4: e1 == Measures.PreImage(f, E) by {
      forall s ensures Model.Sample(n / 2)(s).rest in E <==> f(s) in E {
      }
    }

    assert E in Rand.eventSpace && Rand.prob(E) == 0.5 by {
      assert E == (iset s | Rand.Head(s) == (m % 2 == 1));
      Rand.CoinHasProbOneHalf(m % 2 == 1);
    }

    assert Indep: Rand.prob(e1 * e2) == Rand.prob(e1) * Rand.prob(e2) by {
      assert Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2) by {
        assert Monad.IsIndepFunction(Model.Sample(n / 2)) by {
          assert Monad.IsIndep(Model.Sample(n / 2)) by {
            SampleIsIndep(n / 2);
          }
          Monad.IsIndepImpliesIsIndepFunction(Model.Sample(n / 2));
        }
        assert E in Rand.eventSpace;
        assert Monad.IsIndepFunctionCondition(Model.Sample(n / 2), A, E);
      }
      Monad.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert ProbE1: Rand.prob(e1) == 0.5 by {
      calc {
        0.5;
      ==
        Rand.prob(E);
      == { SampleIsMeasurePreserving(n / 2); }
        Rand.prob(Measures.PreImage(f, E));
      == { reveal Eq4; }
        Rand.prob(e1);
      }
    }

    calc {
      Rand.prob(iset s | Model.Sample(n)(s).value == m);
    == { SampleSetEquality(n, m); }
      Rand.prob(e3);
    == { reveal SplitEvent; }
      Rand.prob(e1 * e2);
    == { reveal Indep; }
      Rand.prob(e1) * Rand.prob(e2);
    == { reveal ProbE1; Helper.Congruence(Rand.prob(e1), 0.5, x => x * Rand.prob(e2)); }
      0.5 * Rand.prob(e2);
    ==
      Rand.prob(e2) / 2.0;
    == { reveal Eq2; }
      Rand.prob(iset s | aOf(s) == m / 2) / 2.0;
    == { reveal Eq3; }
      Rand.prob(iset s | Model.Sample(n / 2)(s).value == m / 2) / 2.0;
    }
  }
}
