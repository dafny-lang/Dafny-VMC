/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Correctness {
  import Measures
  import Rationals
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

  lemma {:axiom} CorrectnessLe1(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(iset s | Model.SampleLe1(gamma)(s).Equals(true)) == Exponential.Exp(-gamma.ToReal())

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

  lemma {:axiom} SampleLe1IsIndep(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Independence.IsIndep(Model.SampleLe1(gamma))


  lemma Le1LoopIterCorrectness(gamma: Rationals.Rational, k: nat)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k + 1)})) == gamma.ToReal() / (k + 1) as real
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k + 1)})) == 1.0 - gamma.ToReal() / (k + 1) as real
  {
    var k' := k + 1;
    var denom := k' * gamma.denom;
    var eventTrue := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(true, k')});
    var eventTrue2 := iset s | Bernoulli.Model.Sample(gamma.numer, denom)(s).Equals(true);
    assert eventTrue == eventTrue2;
    assert Rand.prob(eventTrue2) == gamma.numer as real / denom as real by {
      Bernoulli.Correctness.BernoulliCorrectness(gamma.numer, denom, true);
    }
    var eventFalse := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)((true, k)), iset{(false, k')});
    var eventFalse2 := iset s | Bernoulli.Model.Sample(gamma.numer, denom)(s).Equals(false);
    assert eventFalse == eventFalse2;
    assert Rand.prob(eventFalse2) == 1.0 - gamma.numer as real / denom as real by {
      Bernoulli.Correctness.BernoulliCorrectness(gamma.numer, denom, false);
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

  // ExpTerm(gamma, n) is gamma^n / n!, i.e. the n-th term in the power series of the exponential function.
  function ExpTerm(gamma: real, n: nat, start: nat := 1): real
    requires 1 <= start
  {
    NatArith.FactoralPositive(n, start);
    RealArith.Pow(gamma, n) / NatArith.Factorial(n, start) as real
  }

  lemma ExpTermStep(gamma: real, n: nat, start: nat := 1)
    requires start >= 1
    requires n >= 1
    ensures ExpTerm(gamma, n, start) == ExpTerm(gamma, n - 1, start + 1) * (gamma / start as real)
  {
    NatArith.FactoralPositive(n, start);
    var denom := NatArith.Factorial(n, start) as real;
    var denom2 := (start * NatArith.Factorial(n - 1, start + 1)) as real;
    var numer := RealArith.Pow(gamma, n);
    var numer2 := gamma * RealArith.Pow(gamma, n - 1);
    calc {
      numer / denom;
      { assert numer == numer2; }
      numer2 / denom;
      { assert denom == denom2; }
      numer2 / denom2;
    }
  }

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

  lemma Le1LoopCutCorrectness(gamma: Rationals.Rational, k: nat, n: int, fuel: nat)
    decreases fuel
    requires 1 <= k
    requires 0 <= gamma.numer <= gamma.denom
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k))(fuel), iset m: nat | m <= k + n :: (false, m)))
      == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1)
  {
    var resultSet := iset m: nat | m <= k + n :: (false, m);
    var init: (bool, nat) := (true, k);
    var event := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, init)(fuel), resultSet);
    var prob := if n < 0 then 0.0 else if n <= fuel then 1.0 - ExpTerm(gamma.ToReal(), n, k) else 1.0;
    if fuel == 0 {
      assert event == iset{} by {
        forall s ensures s !in event {
          reveal Le1LoopCut();
          assert !Le1LoopCut(gamma, init)(fuel)(s).In(resultSet);
        }
      }
      assert Rand.prob(event) == 0.0 by {
        Rand.ProbIsProbabilityMeasure();
      }
      assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
    } else {
      var k': nat := k + 1;
      // first loop iteration returns `a == true`
      var trueSet := iset{(true, k + 1)};
      var trueEvent := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (true, m));
      var trueEvent2 := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(true, k + 1)});
      assert trueEvent == trueEvent2 by {
        forall s ensures s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (true, m)) <==> s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(true, k + 1)}) {}
      }
      // first loop iteration returns `a == false`
      var falseSet := iset{(false, k + 1)};
      var falseEvent := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (false, m));
      var falseEvent2 := Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(false, k + 1)});
      assert falseEvent == falseEvent2 by {
        forall s ensures s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset m: nat :: (false, m)) <==> s in Monad.BitstreamsWithValueIn(Model.Le1LoopIter(gamma)(init), iset{(false, k + 1)}) {}
      }
      var f: ((bool, nat)) -> Monad.Hurd<(bool, nat)> := (init': (bool, nat)) => Le1LoopCut(gamma, init')(fuel - 1);
      var trueEvent' := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (true, k + 1))(fuel - 1), resultSet);
      var trueRestInEvent := Monad.BitstreamsWithRestIn(Model.Le1LoopIter(gamma)(init), trueEvent');
      var falseEvent' := Monad.BitstreamsWithValueIn(Le1LoopCut(gamma, (false, k + 1))(fuel - 1), resultSet);
      var falseRestInEvent := Monad.BitstreamsWithRestIn(Model.Le1LoopIter(gamma)(init), falseEvent');
      assert event == falseEvent * falseRestInEvent + trueEvent * trueRestInEvent by {
        forall s: Rand.Bitstream ensures Le1LoopCut(gamma, init)(fuel)(s) == Monad.Bind(Model.Le1LoopIter(gamma)(init), f)(s) {
          calc {
            Le1LoopCut(gamma, init)(fuel)(s);
            { reveal Le1LoopCut(); }
            Loops.WhileCut(
              Model.Le1LoopCondition,
              Model.Le1LoopIter(gamma),
              init,
              fuel)(s);
          }
          match Model.Le1LoopIter(gamma)(init)(s) {
          case Diverging =>
          case Result(init', s') =>
            calc {
              Loops.WhileCut(
                Model.Le1LoopCondition,
                Model.Le1LoopIter(gamma),
                init,
                fuel)(s);
              { Loops.WhileCutUnroll(Model.Le1LoopCondition, Model.Le1LoopIter(gamma), init, s, init', s', fuel); }
              Loops.WhileCut(
                Model.Le1LoopCondition,
                Model.Le1LoopIter(gamma),
                init',
                fuel - 1)(s');
              { reveal Le1LoopCut(); }
              Le1LoopCut(gamma, init')(fuel - 1)(s');
            }
          }
        }
        forall s ensures s in event <==> (s in falseEvent2 && s in falseRestInEvent) || (s in trueEvent2 && s in trueRestInEvent) {
          match Model.Le1LoopIter(gamma)(init)(s)
          case Diverging =>
          case Result((a', k'), s') =>
            calc {
              s in event;
              Le1LoopCut(gamma, init)(fuel)(s).In(resultSet);
              Monad.Bind(Model.Le1LoopIter(gamma)(init), f)(s).In(resultSet);
              f((a', k'))(s').In(resultSet);
              (s in falseEvent && f((a', k'))(s').In(resultSet)) || (s in trueEvent && f((a', k'))(s').In(resultSet));
              (s in falseEvent2 && f((a', k'))(s').In(resultSet)) || (s in trueEvent2 && f((a', k'))(s').In(resultSet));
              { assert s in falseEvent2 <==> a' == false && k' == k + 1; assert s in trueEvent2 <==> a' == true && k' == k +1; }
              (s in falseEvent2 && a' == false && k' == k + 1 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet)) || (s in trueEvent2 && a' == true && k' == k + 1 && Le1LoopCut(gamma, (a', k'))(fuel - 1)(s').In(resultSet));
              (s in falseEvent2 && s in falseRestInEvent) || (s in trueEvent2 && s in trueRestInEvent);
            }
        }
      }
      assert (falseEvent * falseRestInEvent) * (trueEvent * trueRestInEvent) == iset{};
      assert Rand.prob(falseEvent) == 1.0 - gamma.ToReal() / k' as real by {
        Le1LoopIterCorrectness(gamma, k);
      }
      assert Rand.prob(falseEvent') == if 0 < n then 1.0 else 0.0 by {
        if 0 < n {
          assert falseEvent' == Measures.SampleSpace() by {
            forall s ensures s in falseEvent' {
              reveal Le1LoopCut();
              assert Le1LoopCut(gamma, (false, k + 1))(fuel - 1)(s) == Monad.Return((false, k + 1))(s);
            }
          }
          assert Rand.prob(falseEvent') == 1.0 by {
            Rand.ProbIsProbabilityMeasure();
          }
        } else {
          assert falseEvent' == iset{} by {
            forall s ensures s !in falseEvent' {
              reveal Le1LoopCut();
              assert Le1LoopCut(gamma, (false, k + 1))(fuel - 1)(s) == Monad.Return((false, k + 1))(s);
              assert (false, k + 1) !in resultSet;
            }
          }
          assert Rand.prob(falseEvent') == 0.0 by {
            Rand.ProbIsProbabilityMeasure();
          }
        }
      }
      assert Rand.prob(trueEvent) == gamma.ToReal() / k' as real by {
        Le1LoopIterCorrectness(gamma, k);
      }
      assert Rand.prob(trueEvent') == if n <= 1 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1) by {
        Le1LoopCutCorrectness(gamma, k', n - 1, fuel - 1);
        assert n >= 1 ==> NatArith.Min(n, fuel) - 1 == NatArith.Min(n - 1, fuel - 1);
      }
      assert Rand.prob(event) == Rand.prob(falseEvent * falseRestInEvent) + Rand.prob(trueEvent * trueRestInEvent) by {
        assume falseEvent * falseRestInEvent in Rand.eventSpace;
        assume trueEvent * trueRestInEvent in Rand.eventSpace;
        Rand.ProbIsProbabilityMeasure();
        Measures.MeasureOfDisjointUnionIsSum(Rand.eventSpace, Rand.prob, falseEvent * falseRestInEvent, trueEvent * trueRestInEvent);
      }
      assert Rand.prob(trueEvent * trueRestInEvent) == Rand.prob(trueEvent) * Rand.prob(trueEvent') by {
        assume Independence.IsIndepFunction(Model.Le1LoopIter(gamma)(init));
        assume trueEvent' in Rand.eventSpace;
        Independence.ResultsIndependent(Model.Le1LoopIter(gamma)(init), trueSet, trueEvent');
      }
      assert Rand.prob(falseEvent * falseRestInEvent) == Rand.prob(falseEvent) * Rand.prob(falseEvent') by {
        assume Independence.IsIndepFunction(Model.Le1LoopIter(gamma)(init));
        assume falseEvent' in Rand.eventSpace;
        Independence.ResultsIndependent(Model.Le1LoopIter(gamma)(init), falseSet, falseEvent');
      }
      calc {
          Rand.prob(event);
          Rand.prob(falseEvent * falseRestInEvent) + Rand.prob(trueEvent * trueRestInEvent);
          Rand.prob(falseEvent) * Rand.prob(falseEvent') + Rand.prob(trueEvent) * Rand.prob(trueEvent');
      }
      if n <= 0 {
        calc {
          Rand.prob(falseEvent) * Rand.prob(falseEvent') + Rand.prob(trueEvent) * Rand.prob(trueEvent');
          { assert Rand.prob(falseEvent') == 0.0; assert Rand.prob(trueEvent') == 0.0; }
          0.0;
        }
      } else {
        if n == 1 {
          NatArith.FactoralPositive(1, k');
          calc {
            Rand.prob(falseEvent) * Rand.prob(falseEvent') + Rand.prob(trueEvent) * Rand.prob(trueEvent');
            1.0 - gamma.ToReal() / k' as real;
            1.0 - RealArith.Pow(gamma.ToReal(), 1) / NatArith.Factorial(1, k') as real;
            1.0 - ExpTerm(gamma.ToReal(), n, k + 1);
          }
          assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
        } else {
          calc {
            Rand.prob(falseEvent) * Rand.prob(falseEvent') + Rand.prob(trueEvent) * Rand.prob(trueEvent');
            (1.0 - gamma.ToReal() / k' as real) * 1.0 + (gamma.ToReal() / k' as real) * (1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1));
            1.0 - gamma.ToReal() / k' as real * ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel) - 1, k' + 1);
            { ExpTermStep(gamma.ToReal(), NatArith.Min(n, fuel), k'); }
            1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
          }
        }
        assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
      }
      assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
    }
    assert Rand.prob(event) == if n <= 0 then 0.0 else 1.0 - ExpTerm(gamma.ToReal(), NatArith.Min(n, fuel), k + 1);
  }

  lemma {:axiom} Le1LoopCorrectness(gamma: Rationals.Rational, k: nat := 0, n: nat := 0)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)((true, k)), iset m: nat :: (true, m))) == 0.0
    ensures
      Rand.prob(Monad.BitstreamsWithValueIn(Model.Le1Loop(gamma)((true, k)), iset m: nat | m > n :: (false, n)))
      == ExpTerm(gamma.ToReal(), n)
}
