/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Correctness {
  import Measures
  import Rationals
  import Sequences
  import Limits
  import Series
  import Helper
  import NatArith
  import RealArith
  import Exponential
  import Rand
  import Monad
  import Independence
  import Loops
  import Bernoulli
  import Model

  lemma Correctness(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    requires 0 < gamma.denom
    decreases gamma.numer
    ensures Rand.prob(iset s | Model.Sample(gamma)(s).Equals(true)) == Exponential.Exp(-gamma.ToReal())
  {
    if gamma.numer <= gamma.denom {
      assert (iset s | Model.Sample(gamma)(s).Equals(true)) == (iset s | Model.SampleLe1(gamma)(s).Equals(true)) by {
        reveal Model.Sample();
      }
      calc {
        Rand.prob(iset s | Model.SampleLe1(gamma)(s).Equals(true));
        { CorrectnessLe1(gamma); }
        Exponential.Exp(-gamma.ToReal());
      }
    } else {
      var trueEvent := iset s | Model.Sample(gamma)(s).Equals(true);
      var firstSampleTrueEvent := iset s | Model.SampleLe1(Rationals.Int(1))(s).Equals(true);
      var gamma' := Rationals.Rational(gamma.numer - gamma.denom, gamma.denom);
      var secondSampleTrueEvent := iset s | Model.Sample(gamma')(s).Equals(true);
      assert decomposeTrueEvent: trueEvent == firstSampleTrueEvent * Monad.BitstreamsWithRestIn(Model.SampleLe1(Rationals.Int(1)), secondSampleTrueEvent) by {
        forall s ensures s in trueEvent <==> s in firstSampleTrueEvent && s in Monad.BitstreamsWithRestIn(Model.SampleLe1(Rationals.Int(1)), secondSampleTrueEvent) {
          SampleTrueIff(gamma, gamma', s, secondSampleTrueEvent);
        }
      }
      assert independence: Rand.prob(trueEvent) == Rand.prob(firstSampleTrueEvent) * Rand.prob(secondSampleTrueEvent) by {
        assert Independence.IsIndepFunction(Model.SampleLe1(Rationals.Int(1))) by {
          SampleLe1IsIndep(Rationals.Int(1));
          Independence.IsIndepImpliesIsIndepFunction(Model.SampleLe1(Rationals.Int(1)));
        }
        assert secondSampleTrueEvent in Rand.eventSpace by {
          assert secondSampleTrueEvent == Monad.BitstreamsWithValueIn(Model.Sample(gamma'), iset{true});
          SampleIsIndep(gamma');
          Independence.IsIndepImpliesMeasurablePreImageBool(Model.Sample(gamma'), iset{true});
        }
        Independence.ResultsIndependent(
          Model.SampleLe1(Rationals.Int(1)),
          iset{true},
          secondSampleTrueEvent);
        assert Monad.BitstreamsWithValueIn(Model.SampleLe1(Rationals.Int(1)), iset{true}) == firstSampleTrueEvent;
        reveal decomposeTrueEvent;
      }
      assert firstProb: Rand.prob(firstSampleTrueEvent) == Exponential.Exp(-1.0) by {
        calc {
          Rand.prob(firstSampleTrueEvent);
          { CorrectnessLe1(Rationals.Int(1)); }
          Exponential.Exp(-1.0);
        }
      }
      assert gammaMinusOne: gamma'.ToReal() == gamma.ToReal() - 1.0 by {
        RationalMinusOneFact(gamma, gamma');
      }
      assert secondProb: Rand.prob(secondSampleTrueEvent) == Exponential.Exp(-gamma.ToReal() + 1.0) by {
        calc {
          Rand.prob(secondSampleTrueEvent);
          { Correctness(gamma'); }
          Exponential.Exp(-gamma'.ToReal());
          { reveal gammaMinusOne; }
          Exponential.Exp(-(gamma.ToReal() - 1.0));
          Exponential.Exp(-gamma.ToReal() + 1.0);
        }
      }
      calc {
        Rand.prob(iset s | Model.Sample(gamma)(s).Equals(true));
        Rand.prob(trueEvent);
        { reveal independence; }
        Rand.prob(firstSampleTrueEvent) * Rand.prob(secondSampleTrueEvent);
        { reveal firstProb; reveal secondProb; }
        Exponential.Exp(-1.0) * Exponential.Exp(-gamma.ToReal() + 1.0);
        { Exponential.FunctionalEquation(-1.0, -gamma.ToReal() + 1.0); }
        Exponential.Exp(-gamma.ToReal());
      }
    }
  }

  lemma RationalMinusOneFact(gamma: Rationals.Rational, gamma': Rationals.Rational)
    requires gamma.numer > gamma.denom
    requires gamma.denom == gamma'.denom
    requires gamma'.numer == gamma.numer - gamma.denom
    ensures gamma'.ToReal() == gamma.ToReal() - 1.0
  {
    var numer := gamma.numer as real;
    var denom := gamma.denom as real;
    assert denom != 0.0;
    calc {
      gamma'.ToReal();
      gamma'.numer as real / gamma'.denom as real;
      (gamma.numer - gamma.denom) as real / denom;
      (numer - denom) / denom;
      numer / denom - denom / denom;
      numer / denom - 1.0;
      gamma.ToReal() - 1.0;
    }
  }

  lemma SampleTrueIff(gamma: Rationals.Rational, gamma': Rationals.Rational, s: Rand.Bitstream, secondSampleTrueEvent: iset<Rand.Bitstream>)
    requires 0 < gamma.denom < gamma.numer
    requires gamma'.denom == gamma.denom
    requires gamma'.numer == gamma.numer - gamma.denom
    requires forall s' :: s' in secondSampleTrueEvent <==> Model.Sample(gamma')(s').Equals(true)
    ensures Model.Sample(gamma)(s).Equals(true) <==> Model.SampleLe1(Rationals.Int(1))(s).Equals(true) && Model.SampleLe1(Rationals.Int(1))(s).RestIn(secondSampleTrueEvent)
  {
    reveal Model.Sample();
    if Model.SampleLe1(Rationals.Int(1))(s).Equals(true) {
      var s' := Model.SampleLe1(Rationals.Int(1))(s).rest;
      assert Model.Sample(gamma)(s) == Model.Sample(gamma')(s');
      assert Model.Sample(gamma')(s').Equals(true) <==> s' in secondSampleTrueEvent;
    } else {
      assert !Model.Sample(gamma)(s).Equals(true);
    }
  }

  lemma SampleIsIndep(gamma: Rationals.Rational)
    requires 0 <= gamma.numer
    decreases gamma.numer
    ensures Independence.IsIndep(Model.Sample(gamma))
  {
    reveal Model.Sample();
    if gamma.numer <= gamma.denom {
      SampleLe1IsIndep(gamma);
    } else {
      SampleLe1IsIndep(Rationals.Int(1));
      var gamma' := Rationals.Rational(gamma.numer - gamma.denom, gamma.denom);
      var f: bool -> Monad.Hurd<bool> :=
        (b: bool) =>
          var res: Monad.Hurd<bool> :=
            if b
            then Model.Sample(Rationals.Rational(gamma.numer - gamma.denom, gamma.denom))
            else Monad.Return(false);
          res;
      forall b: bool ensures Independence.IsIndep(f(b)) {
        if b {
          SampleIsIndep(gamma');
        } else {
          Independence.ReturnIsIndep(false);
        }
      }
      assert Independence.IsIndep(Model.Sample(gamma)) by {
        assert Model.Sample(gamma) == Monad.Bind(Model.SampleLe1(Rationals.Int(1)), f);
        Independence.BindIsIndep(Model.SampleLe1(Rationals.Int(1)), f);
      }
    }
  }

  lemma CorrectnessLe1(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(iset s | Model.SampleLe1(gamma)(s).Equals(true)) == Exponential.Exp(-gamma.ToReal())
  {
    var event := Monad.BitstreamsWithValueIn(Model.SampleLe1(gamma), iset{true});
    var resultSeq := (k: nat) => if k % 2 == 0 then iset{} else iset ak: (bool, nat) | ak.1 == k;
    var resultSet := Measures.CountableUnion(resultSeq);
    var partEvent := (k: nat) => Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)((true, 0)), resultSeq(k));
    var probPartEvent := (k: nat) => Rand.prob(partEvent(k));
    assert event == Measures.CountableUnion(partEvent) by {
      forall s ensures s in event <==> s in Measures.CountableUnion(partEvent) {
        forall k: nat ensures s in partEvent(k) <==> Model.Le1Loop(gamma)((true, 0))(s).In(resultSeq(k)) {}
        var oddNats := iset ak: (bool, nat) | ak.1 % 2 == 1;
        var oddNats2 := iset k: nat, ak <- resultSeq(k) :: ak;
        assert oddNats == oddNats2 by {
          forall ak: (bool, nat) ensures ak in oddNats <==> ak in oddNats2 {
            calc {
              ak in oddNats;
              ak.1 % 2 == 1;
              ak in resultSeq(ak.1);
            }
          }
        }
        calc {
          s in event;
          Model.SampleLe1(gamma)(s).Equals(true);
          Model.Le1Loop(gamma)((true, 0))(s).Satisfies((ak: (bool, nat)) => ak.1 % 2 == 1);
          Model.Le1Loop(gamma)((true, 0))(s).In(oddNats);
          Model.Le1Loop(gamma)((true, 0))(s).In(oddNats2);
          exists k: nat :: Model.Le1Loop(gamma)((true, 0))(s).In(resultSeq(k));
          exists k: nat :: s in partEvent(k);
        }
      }
    }
    assert Measures.PairwiseDisjoint(partEvent) by {
      forall m: nat, n: nat | m != n ensures partEvent(m) * partEvent(n) == iset{} {}
    }
    forall k: nat ensures probPartEvent(k) == Le1SeriesTerm(gamma.ToReal())(k) {
      if k % 2 == 0 {
        assert partEvent(k) == iset{};
        assert probPartEvent(k) == 0.0 by {
          Rand.ProbIsProbabilityMeasure();
        }
      } else {
        assert probPartEvent(k) == Le1SeriesTerm(gamma.ToReal())(k) by {
          Le1LoopCorrectnessEq(gamma, k);
        }
      }
    }
    assert Series.SumsTo(probPartEvent, Rand.prob(event)) by {
      Rand.ProbIsProbabilityMeasure();
      assume {:axiom} forall k: nat :: partEvent(k) in Rand.eventSpace;
      Measures.MeasureOfCountableDisjointUnionIsSum(Rand.eventSpace, Rand.prob, partEvent, probPartEvent);
    }
    assert Series.SumsTo(probPartEvent, Exponential.Exp(-gamma.ToReal())) by {
      assert Series.SumsTo(Le1SeriesTerm(gamma.ToReal()), Exponential.Exp(-gamma.ToReal())) by {
        Le1SeriesConvergesToExpNeg(gamma.ToReal());
      }
      Series.SumOfEqualsIsEqual(Le1SeriesTerm(gamma.ToReal()), probPartEvent, Exponential.Exp(-gamma.ToReal()));
    }
    Series.SumIsUnique(probPartEvent, Rand.prob(event), Exponential.Exp(-gamma.ToReal()));
    assert event == iset s | Model.SampleLe1(gamma)(s).Equals(true);
  }

  lemma {:axiom} SampleLe1IsIndep(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Independence.IsIndep(Model.SampleLe1(gamma))


  // Proves the correctness of `Model.Le1LoopIter`.
  // Correctness means that when run on an initial value of `(true, k)` it produces
  // (true, k + 1) with probability gamma / (k + 1)
  // (false, k + 1) with probability 1 - gamma / (k + 1)
  // and (implicitly) all other probabilities are zero.
  lemma Le1LoopIterCorrectness(gamma: Rationals.Rational, k: nat)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k + 1)})) == gamma.ToReal() / (k + 1) as real
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k + 1)})) == 1.0 - gamma.ToReal() / (k + 1) as real
  {
    var k': nat := k + 1;
    var denom: nat := k' * gamma.denom;
    assert denom >= 1;
    var eventTrue := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k')});
    var eventTrue2 := iset s | Bernoulli.Model.Sample(gamma.numer, denom)(s).Equals(true);
    assert eventTrue == eventTrue2;
    assert Rand.prob(eventTrue2) == gamma.numer as real / denom as real by {
      Bernoulli.Correctness.BernoulliCorrectness(gamma.numer, denom, true);
      reveal Bernoulli.Correctness.BernoulliMass();
    }
    var eventFalse := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k')});
    var eventFalse2 := iset s | Bernoulli.Model.Sample(gamma.numer, denom)(s).Equals(false);
    assert eventFalse == eventFalse2;
    assert Rand.prob(eventFalse2) == 1.0 - gamma.numer as real / denom as real by {
      Bernoulli.Correctness.BernoulliCorrectness(gamma.numer, denom, false);
      reveal Bernoulli.Correctness.BernoulliMass();
    }
    assert gamma.numer as real / denom as real == gamma.ToReal() / k' as real by {
      calc {
        gamma.ToReal() / k' as real;
        (gamma.numer as real / gamma.denom as real) / k' as real;
        { RealArith.DivMulEqualsDivDiv(gamma.numer as real, gamma.denom as real, k' as real); }
        gamma.numer as real / (gamma.denom as real * k' as real);
        gamma.numer as real / (denom as real);
      }
    }
  }

  // Sequence of terms of the infinite series used in the correctness proof.
  function Le1SeriesTerm(gamma: real): nat -> real {
    (n: nat) => if n % 2 == 0 then 0.0 else Exponential.ExpTerm(gamma, n - 1) - Exponential.ExpTerm(gamma, n)
  }

  lemma {:axiom} Le1SeriesConvergesToExpNeg(gamma: real)
    ensures Series.SumsTo(Le1SeriesTerm(gamma), Exponential.Exp(-gamma))

  // A bounded version of `Model.Le1Loop`.
  opaque ghost function Le1LoopCut(gamma: Rationals.Rational, ak: (bool, nat)): nat -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    (fuel: nat) => Loops.WhileCut(
        Model.Le1LoopCondition,
        Model.Le1LoopIter(gamma),
        ak,
        fuel
      )
  }

  // Decomposes the probability of `Le1LoopCut(gamma, (true, k))(fuel)` producing a value (false, m) with m <= k + n,
  // by branching on the result of the sample `a` from the first loop iteration.
  lemma Le1LoopCutDecomposeProb(gamma: Rationals.Rational, k: nat, n: int, fuel: nat)
    requires 0 <= gamma.numer <= gamma.denom
    requires fuel >= 1
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k))(fuel), iset m: nat | m <= k + n :: (false, m)))
      ==
      Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k + 1)}))
      * Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (false, k + 1))(fuel - 1), iset m: nat | m <= k + n :: (false, m)))
      + Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k + 1)}))
      * Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k + 1))(fuel - 1), iset m: nat | m <= k + n :: (false, m)))
  {
    var resultSet := iset m: nat | m <= k + n :: (false, m);
    var init: (bool, nat) := (true, k);
    var event := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, init)(fuel), resultSet);
    var k': nat := k + 1;
    // first loop iteration returns `a == true`
    var firstIterTrue := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (true, m));
    var firstIterTrue2 := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(true, k + 1)});
    assert firstIterTrue == firstIterTrue2 by {
      forall s ensures s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (true, m)) <==> s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(true, k + 1)}) {}
    }
    var resultAfterFirstTrue := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k + 1))(fuel - 1), resultSet);
    var seedsWithResultAfterFirstTrue := Monad.BitstreamsWithRestIn(Model.Le1LoopIter(gamma)(init), resultAfterFirstTrue);
    // first loop iteration returns `a == false`
    var firstIterFalse := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (false, m));
    var firstIterFalse2 := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(false, k + 1)});
    assert firstIterFalse == firstIterFalse2 by {
      forall s ensures s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (false, m)) <==> s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(false, k + 1)}) {}
    }
    var resultAfterFirstFalse := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (false, k + 1))(fuel - 1), resultSet);
    var seedsWithResultAfterFirstFalse := Monad.BitstreamsWithRestIn(Model.Le1LoopIter(gamma)(init), resultAfterFirstFalse);
    assert decomposeEvent: event == firstIterFalse * seedsWithResultAfterFirstFalse + firstIterTrue * seedsWithResultAfterFirstTrue by {
      forall s ensures s in event <==> (s in firstIterFalse2 && s in seedsWithResultAfterFirstFalse) || (s in firstIterTrue2 && s in seedsWithResultAfterFirstTrue) {
        reveal Le1LoopCut();
        match Model.Le1LoopIter(gamma)(init)(s)
        case Diverging => assert Le1LoopCut(gamma, init)(fuel)(s).Diverging?;
        case Result((a', k'), s') =>
          assert Le1LoopCut(gamma, init)(fuel)(s) == Le1LoopCut(gamma, (a', k'))(fuel - 1)(s');
          calc {
            s in event;
            Le1LoopCut(gamma, init)(fuel)(s).In(resultSet);
            (s in firstIterFalse2 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet)) || (s in firstIterTrue2 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet));
            (s in firstIterFalse2 && a' == false && k' == k + 1 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet)) || (s in firstIterTrue2 && a' == true && k' == k + 1 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet));
            (s in firstIterFalse2 && s in seedsWithResultAfterFirstFalse) || (s in firstIterTrue2 && s in seedsWithResultAfterFirstTrue);
          }
      }
    }
    assert decomposeProb: Rand.prob(event) == Rand.prob(firstIterFalse * seedsWithResultAfterFirstFalse) + Rand.prob(firstIterTrue * seedsWithResultAfterFirstTrue) by {
      assume {:axiom} firstIterFalse * seedsWithResultAfterFirstFalse in Rand.eventSpace;
      assume {:axiom} firstIterTrue * seedsWithResultAfterFirstTrue in Rand.eventSpace;
      Rand.ProbIsProbabilityMeasure();
      assert (firstIterFalse * seedsWithResultAfterFirstFalse) * (firstIterTrue * seedsWithResultAfterFirstTrue) == iset{};
      Measures.MeasureOfDisjointUnionIsSum(Rand.eventSpace, Rand.prob, firstIterFalse * seedsWithResultAfterFirstFalse, firstIterTrue * seedsWithResultAfterFirstTrue);
      reveal decomposeEvent;
    }
    assert trueIndependent: Rand.prob(firstIterTrue * seedsWithResultAfterFirstTrue) == Rand.prob(firstIterTrue) * Rand.prob(resultAfterFirstTrue) by {
      assume {:axiom} Independence.IsIndepFunction(Model.Le1LoopIter(gamma)(init));
      assume {:axiom} resultAfterFirstTrue in Rand.eventSpace;
      Independence.ResultsIndependent(Model.Le1LoopIter(gamma)(init), iset{(true, k + 1)}, resultAfterFirstTrue);
    }
    assert falseIndependent: Rand.prob(firstIterFalse * seedsWithResultAfterFirstFalse) == Rand.prob(firstIterFalse) * Rand.prob(resultAfterFirstFalse) by {
      assume {:axiom} Independence.IsIndepFunction(Model.Le1LoopIter(gamma)(init));
      assume {:axiom} resultAfterFirstFalse in Rand.eventSpace;
      Independence.ResultsIndependent(Model.Le1LoopIter(gamma)(init), iset{(false, k + 1)}, resultAfterFirstFalse);
    }
    calc {
      Rand.prob(event);
      { reveal decomposeProb; }
      Rand.prob(firstIterFalse * seedsWithResultAfterFirstFalse) + Rand.prob(firstIterTrue * seedsWithResultAfterFirstTrue);
      { reveal falseIndependent; reveal trueIndependent; }
      Rand.prob(firstIterFalse) * Rand.prob(resultAfterFirstFalse) + Rand.prob(firstIterTrue) * Rand.prob(resultAfterFirstTrue);
    }
  }

  // Proves correctness of `Le1LoopCut`:
  // i.e. that the probability of `Le1LoopCut(gamma, (true, k))(fuel)` producing a value (false, m) with m <= k + n is
  // (a) 0 if n <= 0 (intuitvely because `k` only increases, so the bound of `k + n` is already passed)
  // (b) 1.0 - gamma^l / (k + 1)^(l) where l = min(n, fuel) and (k + 1)^(l) is the rising factorial (k + 1) * (k + 2) * ... * (k + l)
  lemma Le1LoopCutCorrectness(gamma: Rationals.Rational, k: nat, n: int, fuel: nat)
    decreases fuel
    requires 0 <= gamma.numer <= gamma.denom
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k))(fuel), iset m: nat | m <= k + n :: (false, m)))
      == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1)
  {
    var resultSet := iset m: nat | m <= k + n :: (false, m);
    var event := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k))(fuel), resultSet);
    if fuel == 0 {
      assert event == iset{} by {
        forall s ensures s !in event {
          reveal Le1LoopCut();
          assert !Le1LoopCut(gamma, (true, k))(fuel)(s).In(resultSet);
        }
      }
      assert Rand.prob(event) == 0.0 by {
        Rand.ProbIsProbabilityMeasure();
      }
      assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1) by {
        reveal Exponential.ExpTerm();
        reveal RealArith.Pow();
        reveal NatArith.Factorial();
      }
    } else {
      var k': nat := k + 1;
      var firstIterTrue := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k + 1)});
      var firstIterFalse := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k + 1)});
      var desiredResultAfterFirstIterTrue := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k + 1))(fuel - 1), resultSet);
      var desiredResultAfterFirstIterFalse := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (false, k + 1))(fuel - 1), resultSet);

      assert probFirstFalse: Rand.prob(firstIterFalse) == 1.0 - gamma.ToReal() / k' as real by {
        Le1LoopIterCorrectness(gamma, k);
      }
      assert probResultAfterFirstFalse: Rand.prob(desiredResultAfterFirstIterFalse) == if 0 < n then 1.0 else 0.0 by {
        if 0 < n {
          assert desiredResultAfterFirstIterFalse == Measures.SampleSpace() by {
            forall s ensures s in desiredResultAfterFirstIterFalse {
              reveal Le1LoopCut();
              assert Le1LoopCut(gamma, (false, k + 1))(fuel - 1)(s) == Monad.Return((false, k + 1))(s);
            }
          }
          assert Rand.prob(desiredResultAfterFirstIterFalse) == 1.0 by {
            Rand.ProbIsProbabilityMeasure();
          }
        } else {
          assert desiredResultAfterFirstIterFalse == iset{} by {
            forall s ensures s !in desiredResultAfterFirstIterFalse {
              reveal Le1LoopCut();
              assert Le1LoopCut(gamma, (false, k + 1))(fuel - 1)(s) == Monad.Return((false, k + 1))(s);
              assert (false, k + 1) !in resultSet;
            }
          }
          assert Rand.prob(desiredResultAfterFirstIterFalse) == 0.0 by {
            Rand.ProbIsProbabilityMeasure();
          }
        }
      }
      assert probFirstTrue: Rand.prob(firstIterTrue) == gamma.ToReal() / k' as real by {
        Le1LoopIterCorrectness(gamma, k);
      }
      assert probResultAfterFirstTrue: Rand.prob(desiredResultAfterFirstIterTrue) == if n <= 1 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1) by {
        Le1LoopCutCorrectness(gamma, k', n - 1, fuel - 1);
        assert n >= 1 ==> NatArith.Min(n, fuel) - 1 == NatArith.Min(n - 1, fuel - 1);
      }
      if n <= 0 {
        calc {
          Rand.prob(event);
          { Le1LoopCutDecomposeProb(gamma, k, n, fuel); }
          Rand.prob(firstIterFalse) * Rand.prob(desiredResultAfterFirstIterFalse) + Rand.prob(firstIterTrue) * Rand.prob(desiredResultAfterFirstIterTrue);
          { reveal probResultAfterFirstFalse; reveal probResultAfterFirstTrue; }
          0.0;
        }
      } else {
        if n == 1 {
          NatArith.FactoralPositive(1, k');
          calc {
            Rand.prob(event);
            { Le1LoopCutDecomposeProb(gamma, k, n, fuel); }
            Rand.prob(firstIterFalse) * Rand.prob(desiredResultAfterFirstIterFalse) + Rand.prob(firstIterTrue) * Rand.prob(desiredResultAfterFirstIterTrue);
            { reveal probFirstFalse; reveal probResultAfterFirstFalse; reveal probFirstTrue; reveal probResultAfterFirstTrue; }
            1.0 - gamma.ToReal() / k' as real;
            { reveal RealArith.Pow(); reveal NatArith.Factorial(); }
            1.0 - RealArith.Pow(gamma.ToReal(), 1) / NatArith.Factorial(1, k') as real;
            { reveal Exponential.ExpTerm(); }
            1.0 - Exponential.ExpTerm(gamma.ToReal(), n, k + 1);
          }
          assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
        } else {
          calc {
            Rand.prob(event);
            { Le1LoopCutDecomposeProb(gamma, k, n, fuel); }
            Rand.prob(firstIterFalse) * Rand.prob(desiredResultAfterFirstIterFalse) + Rand.prob(firstIterTrue) * Rand.prob(desiredResultAfterFirstIterTrue);
            { reveal probFirstFalse; reveal probResultAfterFirstFalse; reveal probFirstTrue; reveal probResultAfterFirstTrue; }
            (1.0 - gamma.ToReal() / k' as real) * 1.0 + (gamma.ToReal() / k' as real) * (1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1));
            1.0 - gamma.ToReal() / k' as real * Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1);
            { Exponential.ExpTermStep(gamma.ToReal(), NatArith.Min(n, fuel), k'); }
            1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
          }
        }
        assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
      }
      assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
    }
    assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
  }

  // Proves the first version of correctness of `Model.Le1Loop`:
  // i.e. that the probability of `Model.Le1Loop(gamma)((true, 0))` producing a value (_, m) with m <= n is
  // 1.0 - gamma^n / n!
  lemma Le1LoopCorrectnessLe(gamma: Rationals.Rational, n: nat)
    requires 0 <= gamma.numer <= gamma.denom
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), iset ak: (bool, nat) | ak.1 <= n))
      == 1.0 - Exponential.ExpTerm(gamma.ToReal(), n)
  {
    var resultSet := iset ak: (bool, nat) | ak.1 <= n;
    var resultSetRestricted := iset m: nat | m <= n :: (false, m);
    var limit := 1.0 - Exponential.ExpTerm(gamma.ToReal(), n);
    assert resultSetRestricted == iset a <- resultSet | !Model.Le1LoopCondition(a);
    var sequence: nat -> real := Loops.WhileCutProbability(Model.Le1LoopCondition, Model.Le1LoopIter(gamma), (true, 0), resultSetRestricted);
    assert Limits.ConvergesTo(sequence, limit) by {
      forall fuel: nat | fuel >= n ensures sequence(fuel) == limit {
        calc {
          sequence(fuel);
          Loops.WhileCutProbability(Model.Le1LoopCondition, Model.Le1LoopIter(gamma), (true, 0), resultSetRestricted)(fuel);
          { reveal Le1LoopCut(); }
          Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, 0))(fuel), resultSetRestricted));
          { Le1LoopCutCorrectness(gamma, 0, n, fuel); reveal Exponential.ExpTerm(); reveal RealArith.Pow(); reveal NatArith.Factorial(); }
          1.0 - Exponential.ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel));
          limit;
        }
      }
      Limits.ConstantSequenceConverges(sequence, limit, n);
    }
    reveal Model.Le1Loop();
    assert Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultSet)) == limit by {
      Loops.WhileProbabilityViaLimit(Model.Le1LoopCondition, Model.Le1LoopIter(gamma), (true, 0), resultSet, resultSetRestricted, limit);
    }
  }

  // Proves the second version of correctness of `Model.Le1Loop`:
  // i.e. that the probability of `Model.Le1Loop(gamma)((true, 0))` producing a value (_, n) is
  // 0 if n == 0
  // gamma^(n - 1) / (n - 1)! - gamma^n / n!
  lemma Le1LoopCorrectnessEq(gamma: Rationals.Rational, n: nat := 0)
    requires 0 <= gamma.numer <= gamma.denom
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), iset ak: (bool, nat) | ak.1 == n))
      == if n == 0 then 0.0 else Exponential.ExpTerm(gamma.ToReal(), n - 1) - Exponential.ExpTerm(gamma.ToReal(), n)
  {
    var resultEqN := iset ak: (bool, nat) | ak.1 == n;
    var eventEqN := Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultEqN);
    var resultLeN := iset ak: (bool, nat) | ak.1 <= n;
    var eventLeN := Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultLeN);
    if n == 0 {
      assert resultEqN == resultLeN;
      calc {
        Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultEqN));
        Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultLeN));
        { Le1LoopCorrectnessLe(gamma, n); }
        1.0 - Exponential.ExpTerm(gamma.ToReal(), n);
        { reveal Exponential.ExpTerm(); reveal RealArith.Pow(); reveal NatArith.Factorial(); }
        0.0;
      }
    } else {
      var resultLeN1 := iset ak: (bool, nat) | ak.1 <= n - 1;
      assert resultLeN1 * resultEqN == iset{};
      assert resultLeN1 + resultEqN == resultLeN;
      var eventLeN1 := Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)(((true, 0))), resultLeN1);
      assert eventLeN1 * eventEqN == iset{};
      assert eventLeN1 + eventEqN == eventLeN;
      assert Rand.prob(eventLeN) == Rand.prob(eventLeN1) + Rand.prob(eventEqN) by {
        Rand.ProbIsProbabilityMeasure();
        assume {:axiom} eventLeN1 in Rand.eventSpace;
        assume {:axiom} eventEqN in Rand.eventSpace;
        Measures.MeasureOfDisjointUnionIsSum(Rand.eventSpace, Rand.prob, eventLeN1, eventEqN);
      }
      calc {
        Rand.prob(eventEqN);
        Rand.prob(eventLeN) - Rand.prob(eventLeN1);
        { Le1LoopCorrectnessLe(gamma, n); Le1LoopCorrectnessLe(gamma, n - 1); }
        (1.0 - Exponential.ExpTerm(gamma.ToReal(), n)) - (1.0 - Exponential.ExpTerm(gamma.ToReal(), n - 1));
        Exponential.ExpTerm(gamma.ToReal(), n - 1) - Exponential.ExpTerm(gamma.ToReal(), n);
      }
    }
  }
}
