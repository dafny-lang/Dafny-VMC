/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Helper.dfy"
include "../../Math/MeasureTheory.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "Model.dfy"

module UniformPowerOfTwoCorrectness {
  import Helper
  import Monad
  import Independence
  import RandomNumberGenerator
  import Quantifier
  import WhileAndUntil
  import MeasureTheory
  import Model = UniformPowerOfTwoModel

  /************
   Definitions
  ************/

  ghost predicate UnifIsCorrect(n: nat, k: nat, m: nat)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
  {
    RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == if m < Helper.Power(2, k) then 1.0 / (Helper.Power(2, k) as real) else 0.0
  }

  function Sample1(n: nat): RandomNumberGenerator.RNG -> RandomNumberGenerator.RNG
    requires n >= 1
  {
    (s: RandomNumberGenerator.RNG) => Model.Sample(n)(s).1
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
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == if m < Helper.Power(2, Helper.Log2Floor(n)) then 1.0 / (Helper.Power(2, Helper.Log2Floor(n)) as real) else 0.0
  {
    var e := iset s | Model.Sample(n)(s).0 == m;
    var k := Helper.Log2Floor(n);

    assert e in RandomNumberGenerator.event_space by {
      assert iset{m} in MeasureTheory.natEventSpace;
      var preimage := MeasureTheory.PreImage((s: RandomNumberGenerator.RNG) => Model.Sample(n)(s).0, iset{m});
      assert preimage in RandomNumberGenerator.event_space by {
        assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, MeasureTheory.natEventSpace, s => Model.Sample(n)(s).0) by {
          SampleIsIndepFn(n);
          Independence.IsIndepFnImpliesFstMeasurableNat(Model.Sample(n));
        }
      }
      assert e == preimage;
    }

    if k == 0 {
      assert n == 1;
      UnifCorrectness(n, k);
      assert UnifIsCorrect(n, k, m);
    } else {
      assert n > 1;
      Helper.Power2OfLog2Floor(n);
      UnifCorrectness(n, k);
      assert UnifIsCorrect(n, k, m);
    }
  }

  // See PROB_BERN_UNIF_LT in HOL implementation.
  lemma UnifCorrectness2Inequality(n: nat, m: nat)
    requires n >= 1
    requires m <= Helper.Power(2, Helper.Log2Floor(n))
    ensures
      var e := iset s | Model.Sample(n)(s).0 < m;
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == (m as real) / (Helper.Power(2, Helper.Log2Floor(n)) as real)
  {
    var e := iset s | Model.Sample(n)(s).0 < m;

    if m == 0 {
      assert e == iset{};
      RandomNumberGenerator.RNGHasMeasure();
    } else {
      var e1 := iset s | Model.Sample(n)(s).0 < m-1;
      var e2 := iset s | Model.Sample(n)(s).0 == m-1;
      assert e1 in RandomNumberGenerator.event_space by {
        UnifCorrectness2Inequality(n, m-1);
      }
      assert e2 in RandomNumberGenerator.event_space by {
        UnifCorrectness2(n, m-1);
      }
      assert e in RandomNumberGenerator.event_space by {
        assert e == e1 + e2;
        RandomNumberGenerator.RNGHasMeasure();
        MeasureTheory.BinaryUnion(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space, e1, e2);
      }
      calc {
        RandomNumberGenerator.mu(e);
        { assert e == e1 + e2; }
        RandomNumberGenerator.mu(e1 + e2);
        { assert e1 * e2 == iset{}; RandomNumberGenerator.RNGHasMeasure(); MeasureTheory.PosCountAddImpliesAdd(RandomNumberGenerator.event_space, RandomNumberGenerator.sample_space, RandomNumberGenerator.mu); assert MeasureTheory.IsAdditive(RandomNumberGenerator.event_space, RandomNumberGenerator.mu); }
        RandomNumberGenerator.mu(e1) + RandomNumberGenerator.mu(e2);
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
        UnifCorrectnessCaseNOne(m);
      } else {
        if m % 2 == 0 {
          UnifCorrectnessCaseMEven(n, k, m / 2);
        } else {
          UnifCorrectnessCaseMOdd(n, k, m / 2);
        }
      }
    }
  }

  lemma UnifCorrectnessCaseNOne(m: nat)
    ensures UnifIsCorrect(1, 0, m)
  {
    assert Helper.Power(2, 0) == 1;
    if m == 0 {
      assert (iset s | Model.Sample(1)(s).0 == m) == (iset s);
    } else {
      assert (iset s | Model.Sample(1)(s).0 == m) == iset{};
    }
    RandomNumberGenerator.RNGHasMeasure();
  }

  lemma UnifCorrectnessCaseMEven(n: nat, k: nat, u: nat)
    requires k >= 1
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures UnifIsCorrect(n, k, 2 * u)
  {
    var m := 2 * u;
    calc {
      RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
    == { SampleCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2 * Model.Sample(n / 2)(s).0 == m) / 2.0;
    == { assert (iset s | 2 * Model.Sample(n / 2)(s).0 == m) == (iset s | Model.Sample(n / 2)(s).0 == u); }
      RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
    }
    if m < Helper.Power(2, k) {
      assert RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) == 1.0 / (Helper.Power(2, k - 1) as real) by {
        UnifCorrectness(n / 2, k - 1);
        assert UnifIsCorrect(n / 2, k - 1, u);
      }
      calc {
        RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
      ==
        (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
      == { Helper.PowerOfTwoLemma(k - 1); }
        1.0 / (Helper.Power(2, k) as real);
      }
      assert UnifIsCorrect(n / 2, k - 1, u);
    } else {
      assert u >= Helper.Power(2, k - 1);
      UnifCorrectness(n / 2, k - 1);
      assert UnifIsCorrect(n / 2, k - 1, u);
      assert RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == 0.0;
    }
  }

  lemma UnifCorrectnessCaseMOdd(n: nat, k: nat, u: nat)
    requires k >= 1
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures UnifIsCorrect(n, k, 2 * u + 1)
  {
    var m := 2 * u + 1;
    calc {
      RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
    == { SampleCaseSplit(n, m); }
      RandomNumberGenerator.mu(iset s | 2 * Model.Sample(n / 2)(s).0 + 1 == m) / 2.0;
    == { assert (iset s | 2 * Model.Sample(n / 2)(s).0 + 1 == m) == (iset s | Model.Sample(n / 2)(s).0 == u); }
      RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
    }
    if m < Helper.Power(2, k) {
      assert RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) == 1.0 / (Helper.Power(2, k - 1) as real) by {
        assert u < Helper.Power(2, k - 1);
        UnifCorrectness(n / 2, k - 1);
        assert UnifIsCorrect(n / 2, k - 1, u);
      }
      calc {
        RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
      ==
        RandomNumberGenerator.mu(iset s | Model.Sample(n / 2)(s).0 == u) / 2.0;
      ==
        (1.0 / Helper.Power(2, k - 1) as real) / 2.0;
      == { Helper.PowerOfTwoLemma(k - 1); }
        1.0 / (Helper.Power(2, k) as real);
      }
      assert UnifIsCorrect(n, k, m);
    } else {
      assert u >= Helper.Power(2, k - 1);
      UnifCorrectness(n / 2, k - 1);
      assert UnifIsCorrect(n / 2, k - 1, u);
      assert RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == 0.0;
    }
  }

  // Equation (4.7)
  lemma SampleIsIndepFn(n: nat)
    requires n >= 1
    decreases n
    ensures Independence.IsIndepFn(Model.Sample(n))
  {
    var fn := Model.Sample(n);
    if n == 1 {
      Independence.ReturnIsIndepFn(0 as nat);
    } else {
      assert Independence.IsIndepFn(Model.Sample(n / 2)) by {
        SampleIsIndepFn(n / 2);
      }
      forall m: nat ensures Independence.IsIndepFn(Model.UnifStep(m)) {
        Independence.DeconstructIsIndepFn();
        var g := Model.UnifStepHelper(m);
        forall b: bool ensures Independence.IsIndepFn(g(b)) {
          Independence.ReturnIsIndepFn((if b then 2 * m + 1 else 2 * m) as nat);
        }
        Independence.IndepFnIsCompositional(Monad.Deconstruct, g);
      }
      Independence.IndepFnIsCompositional(Model.Sample(n / 2), Model.UnifStep);
    }
  }

  lemma SampleIsMeasurePreserving(n: nat)
    requires n >= 1
    ensures MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, Sample1(n))
  {
    var f := Sample1(n);
    assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.event_space, f) by {
      SampleIsIndepFn(n);
      Independence.IsIndepFnImpliesSndMeasurable(Model.Sample(n));
      assert Independence.IsIndepFn(Model.Sample(n));
    }
    if n == 1 {
      forall e | e in RandomNumberGenerator.event_space ensures RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) {
        forall s: RandomNumberGenerator.RNG ensures f(s) == s {
          assert f(s) == s;
        }
        MeasureTheory.PreImageIdentity(f, e);
      }
      assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, f);
    } else {
      var g := Sample1(n / 2);
      forall e | e in RandomNumberGenerator.event_space ensures RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) {
        var e' := (iset s | Monad.Tail(s) in e);
        assert e' in RandomNumberGenerator.event_space by {
          assert e' == MeasureTheory.PreImage(Monad.Tail, e);
          Monad.TailIsMeasurePreserving();
          assert MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.event_space, Monad.Tail);
        }
        assert MeasureTheory.PreImage(f, e) == MeasureTheory.PreImage(g, e') by {
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
          MeasureTheory.PreImagesEqual(f, e, g, e');
        }
        assert RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e)) == RandomNumberGenerator.mu(e) by {
          calc {
            RandomNumberGenerator.mu(MeasureTheory.PreImage(f, e));
          ==
            RandomNumberGenerator.mu(MeasureTheory.PreImage(g, e'));
          == { SampleIsMeasurePreserving(n / 2); assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, g); assert e' in RandomNumberGenerator.event_space; }
            RandomNumberGenerator.mu(e');
          == { assert e' == MeasureTheory.PreImage(Monad.Tail, e); }
            RandomNumberGenerator.mu(MeasureTheory.PreImage(Monad.Tail, e));
          == { Monad.TailIsMeasurePreserving(); }
            RandomNumberGenerator.mu(e);
          }
        }
      }
      assert MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, f);
    }
  }

  lemma SampleTailDecompose(n: nat, s: RandomNumberGenerator.RNG)
    requires n >= 2
    ensures Model.Sample(n)(s).1 == Monad.Tail(Model.Sample(n / 2)(s).1)
  {
    var (a, s') := Model.Sample(n / 2)(s);
    var (b, s'') := Monad.Deconstruct(s');
    calc {
      Model.Sample(n)(s).1;
    ==
      Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).1;
    ==
      Model.UnifStep(a)(s').1;
    ==
      Monad.Bind(Monad.Deconstruct, (b: bool) => Monad.Return(if b then 2*a + 1 else 2*a))(s').1;
    ==
      Monad.Return(if b then 2*a + 1 else 2*a)(s'').1;
    ==
      s'';
    ==
      Monad.Tail(s');
    ==
      Monad.Tail(Model.Sample(n / 2)(s).1);
    }
  }

  lemma SampleCorrectnessIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires n >= 2
    ensures
      var a := Model.Sample(n / 2)(s).0;
      var b := Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
      Model.Sample(n)(s).0 == m
      <==>
      (b && 2*a + 1 == m) || (!b && 2*a == m)
  {
    var (a, s') := Model.Sample(n / 2)(s);
    var (b, s'') := Monad.Deconstruct(s');
    calc {
      Model.Sample(n)(s).0;
    ==
      Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s).0;
    ==
      Model.UnifStep(a)(s').0;
    ==
      Monad.Bind(Monad.Deconstruct, b => Monad.Return(if b then 2*a + 1 else 2*a))(s').0;
    ==
      Monad.Return(if b then 2*a + 1 else 2*a)(s'').0;
    ==
      if b then 2*a + 1 else 2*a;
    }
  }

  lemma SampleCorrectnessEvenCaseIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires m % 2 == 0
    requires n >= 2
    ensures
      var a := Model.Sample(n / 2)(s).0;
      var b := Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
      Model.Sample(n)(s).0 == m <==> (!b && 2*a == m)
  {
    var a: nat := Model.Sample(n / 2)(s).0;
    var b := Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    if Model.Sample(n)(s).0 == m {
      if (b && 2*a + 1 == m) {
        assert m % 2 == 1 by {
          Helper.DivModAddMultiple(2, 1, a);
        }
        assert m % 2 == 0;
        assert false;
      }
      assert !(b && 2*a + 1 == m) ==> (!b && 2*a == m) by {
        SampleCorrectnessIff(n, s, m);
        assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      }
    }
    if (!b && 2*a == m) {
      assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      assert Model.Sample(n)(s).0 == m by { SampleCorrectnessIff(n, s, m); }
    }
  }

  lemma SampleOddCaseIff(n: nat, s: RandomNumberGenerator.RNG, m: nat)
    requires m % 2 == 1
    requires n >= 2
    ensures
      var a := Model.Sample(n / 2)(s).0;
      var b := Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
      Model.Sample(n)(s).0 == m <==> (b && 2*a + 1 == m)
  {
    var a := Model.Sample(n / 2)(s).0;
    var b := Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    if Model.Sample(n)(s).0 == m {
      if (!b && 2*a == m) {
        assert m % 2 == 0 by { assert m / 2 == a; }
        assert m % 2 == 1;
      }
      assert !(!b && 2*a == m) ==> (b && 2*a + 1 == m) by {
        SampleCorrectnessIff(n, s, m);
        assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      }
    }
    if (b && 2*a + 1 == m) {
      assert (b && 2*a + 1 == m) || (!b && 2*a == m);
      assert Model.Sample(n)(s).0 == m by { SampleCorrectnessIff(n, s, m); }
    }
  }

  lemma SampleEvenCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 0
    requires n >= 2
    ensures
      var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
      var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
      (iset s | Model.Sample(n)(s).0 == m) == (iset s | !b_of(s) && 2*a_of(s) == m)
  {
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
    forall s ensures Model.Sample(n)(s).0 == m <==> (!b_of(s) && 2*a_of(s) == m) {
      SampleCorrectnessEvenCaseIff(n, s, m);
    }
  }

  lemma SampleOddCaseSetEquality(n: nat, m: nat)
    requires m % 2 == 1
    requires n >= 2
    ensures
      var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
      var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
      (iset s | Model.Sample(n)(s).0 == m) == (iset s | b_of(s) && 2*a_of(s) + 1 == m)
  {
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
    forall s ensures Model.Sample(n)(s).0 == m <==> (b_of(s) && 2*a_of(s) + 1 == m) {
      SampleOddCaseIff(n, s, m);
    }
  }

  lemma {:vcs_split_on_every_assert} SampleEvenCase(n: nat, m: nat)
    requires m % 2 == 0
    requires n >= 2
    ensures RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 == m) / 2.0
  {
    var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x == m);
    var E: iset<RandomNumberGenerator.RNG> := (iset s | Monad.Deconstruct(s).0 == false);
    var f := Sample1(n / 2);

    var e1 := (iset s | Sample1(n / 2)(s) in E);
    var e2 := (iset s | Model.Sample(n / 2)(s).0 in A);

    assert Eq1: (iset s | !b_of(s)) == e1 by {
      forall s ensures !b_of(s) <==> Model.Sample(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) == m) == e2 by {
      forall s ensures 2*a_of(s) == m <==> Model.Sample(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) == m) == (iset s | 2*Model.Sample(n / 2)(s).0 == m) by {
      forall s ensures 2*a_of(s) == m <==> 2*Model.Sample(n / 2)(s).0 == m {
      }
    }

    assert Eq4: e1 == MeasureTheory.PreImage(Sample1(n / 2), E) by {
      forall s ensures Model.Sample(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert EMeasure: E in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(E) == 0.5 by {
      assert E == (iset s | Monad.Head(s) == false);
      Monad.HeadIsMeasurable(false);
    }

    assert Indep: RandomNumberGenerator.mu(e1 * e2) == RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) by {
      assert e1 == (iset s | Model.Sample(n / 2)(s).1 in E) by {
        forall s ensures s in e1 <==> Model.Sample(n / 2)(s).1 in E {
        }
      }
      assert MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2) by {
        assert Independence.IsIndepFunction(Model.Sample(n / 2)) by {
          assert Independence.IsIndepFn(Model.Sample(n / 2)) by {
            SampleIsIndepFn(n / 2);
          }
          Independence.IsIndepFnImpliesIsIndepFunction(Model.Sample(n / 2));
        }
        assert E in RandomNumberGenerator.event_space by { reveal EMeasure; }
        assert Independence.IsIndepFunctionCondition(Model.Sample(n / 2), A, E);
      }
      Independence.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == RandomNumberGenerator.mu(e1) by {
      calc {
        0.5;
      == { reveal EMeasure; }
        RandomNumberGenerator.mu(E);
      == { reveal EMeasure; SampleIsMeasurePreserving(n / 2); }
        RandomNumberGenerator.mu(MeasureTheory.PreImage(Sample1(n / 2), E));
      == { reveal Eq4; }
        RandomNumberGenerator.mu(e1);
      }
    }

    assert Inter: (iset s | !b_of(s) && 2*a_of(s) == m) == (iset s | !b_of(s)) * (iset s | 2*a_of(s) == m) by {
      forall s ensures !b_of(s) && 2*a_of(s) == m <==> !b_of(s) && 2*a_of(s) == m {
      }
    }

    assert MulSub: RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2) by {
      reveal EMeasure;
      assert RandomNumberGenerator.mu(e1) == 0.5 by { reveal Prob; }
      assert RandomNumberGenerator.mu(e1) == 0.5 ==> RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2);
    }

    calc {
      RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
    == { SampleEvenCaseSetEquality(n, m); }
      RandomNumberGenerator.mu(iset s | !b_of(s) && 2*a_of(s) == m);
    == {  reveal Inter; }
      RandomNumberGenerator.mu((iset s | !b_of(s)) * (iset s | 2*a_of(s) == m));
    == { reveal Eq1; reveal Eq2; }
      RandomNumberGenerator.mu(e1 * e2);
    == { reveal Indep; }
      RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2);
    == { reveal MulSub; }
      0.5 * RandomNumberGenerator.mu(e2);
    == { Helper.DivisionByTwo(RandomNumberGenerator.mu(e2)); }
      RandomNumberGenerator.mu(e2) / 2.0;
    == { reveal Eq2; }
      RandomNumberGenerator.mu(iset s | 2*a_of(s) == m) / 2.0;
    == { reveal Eq3; }
      RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 == m) / 2.0;
    }
  }

  lemma SampleOddCase(n: nat, m: nat)
    requires m % 2 == 1
    requires n >= 2
    ensures RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 + 1 == m) / 2.0
  {
    var a_of := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).0;
    var b_of := (s: RandomNumberGenerator.RNG) => Monad.Deconstruct(Model.Sample(n / 2)(s).1).0;
    var A: iset<nat> := (iset x | 2*x + 1 == m);
    var E: iset<RandomNumberGenerator.RNG> := (iset s | Monad.Deconstruct(s).0 == true);
    var f := (s: RandomNumberGenerator.RNG) => Model.Sample(n / 2)(s).1;

    var e1 := (iset s | Model.Sample(n / 2)(s).1 in E);
    var e2 := (iset s | Model.Sample(n / 2)(s).0 in A);

    assert Eq1: (iset s | b_of(s)) == e1 by {
      forall s ensures b_of(s) <==> Model.Sample(n / 2)(s).1 in E {
      }
    }

    assert Eq2: (iset s | 2*a_of(s) + 1 == m) == e2 by {
      forall s ensures 2*a_of(s) + 1 == m <==> Model.Sample(n / 2)(s).0 in A {
      }
    }

    assert Eq3: (iset s | 2*a_of(s) + 1 == m) == (iset s | 2*Model.Sample(n / 2)(s).0 + 1 == m) by {
      forall s ensures 2*a_of(s) + 1 == m <==> 2*Model.Sample(n / 2)(s).0 + 1 == m {
      }
    }

    assert Eq4: e1 == MeasureTheory.PreImage(f, E) by {
      forall s ensures Model.Sample(n / 2)(s).1 in E <==> f(s) in E {
      }
    }

    assert E in RandomNumberGenerator.event_space && RandomNumberGenerator.mu(E) == 0.5 by {
      assert E == (iset s | Monad.Head(s) == true);
      Monad.HeadIsMeasurable(true);
    }

    assert Indep: RandomNumberGenerator.mu(e1 * e2) == RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) by {
      assert MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2) by {
        assert Independence.IsIndepFunction(Model.Sample(n / 2)) by {
          assert Independence.IsIndepFn(Model.Sample(n / 2)) by {
            SampleIsIndepFn(n / 2);
          }
          Independence.IsIndepFnImpliesIsIndepFunction(Model.Sample(n / 2));
        }
        assert E in RandomNumberGenerator.event_space;
        assert Independence.IsIndepFunctionCondition(Model.Sample(n / 2), A, E);
      }
      Independence.AreIndepEventsConjunctElimination(e1, e2);
    }

    assert Prob: 0.5 == RandomNumberGenerator.mu(e1) by {
      calc {
        0.5;
      ==
        RandomNumberGenerator.mu(E);
      == { SampleIsMeasurePreserving(n / 2); }
        RandomNumberGenerator.mu(MeasureTheory.PreImage(f, E));
      == { reveal Eq4; }
        RandomNumberGenerator.mu(e1);
      }
    }

    assert Prob2: RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2) == 0.5 * RandomNumberGenerator.mu(e2) by {
      reveal Prob;
    }

    calc {
      RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m);
    == { SampleOddCaseSetEquality(n, m); }
      RandomNumberGenerator.mu(iset s | b_of(s) && 2*a_of(s) + 1 == m);
    == { assert (iset s | b_of(s) && 2*a_of(s) + 1 == m) == (iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m); }
      RandomNumberGenerator.mu((iset s | b_of(s)) * (iset s | 2*a_of(s) + 1 == m));
    == { reveal Eq1; reveal Eq2; }
      RandomNumberGenerator.mu(e1 * e2);
    == { reveal Indep; }
      RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2);
    == { reveal Prob2; }
      0.5 * RandomNumberGenerator.mu(e2);
    ==
      RandomNumberGenerator.mu(e2) / 2.0;
    == { reveal Eq2; }
      RandomNumberGenerator.mu(iset s | 2*a_of(s) + 1 == m) / 2.0;
    == { reveal Eq3; }
      RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 + 1 == m) / 2.0;
    }
  }

  lemma SampleCaseSplit(n: nat, m: nat)
    requires n >= 2
    ensures RandomNumberGenerator.mu(iset s | Model.Sample(n)(s).0 == m) == if m % 2 == 0 then RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 == m) / 2.0 else RandomNumberGenerator.mu(iset s | 2*Model.Sample(n / 2)(s).0 + 1 == m) / 2.0
  {
    if m % 2 == 0 {
      SampleEvenCase(n, m);
    } else {
      SampleOddCase(n, m);
    }
  }

}
