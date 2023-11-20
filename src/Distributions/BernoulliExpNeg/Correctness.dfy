/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Correctness {
  import Rationals
  import Exponential
  import Rand
  import Monad
  import Independence
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
      var f: bool -> Monad.Hurd<bool> := (b: bool) => if b then Model.Sample(gamma') else Monad.Return(false);
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
        assert forall b: bool :: Independence.IsIndepFunction(f(b)) by {
          forall b: bool ensures Independence.IsIndepFunction(f(b)) {
            assert Independence.IsIndep(f(b)) by {
              if b {
                SampleIsIndep(gamma');
              } else {
                Independence.ReturnIsIndep(false);
              }
            }
            Independence.IsIndepImpliesIsIndepFunction(f(b));
          }
        }
        assert secondSampleTrueEvent in Rand.eventSpace by {
          assert secondSampleTrueEvent == Monad.BitstreamsWithValueIn(Model.Sample(gamma'), iset{true});
          SampleIsIndep(gamma');
          Independence.IsIndepImpliesMeasurablePreImageBool(Model.Sample(gamma'), iset{true});
        }
        Independence.ResultsIndependent(
          Model.SampleLe1(Rationals.Int(1)),
          f,
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

}
