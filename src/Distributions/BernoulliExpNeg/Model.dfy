/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BernoulliExpNeg.Model {
  import Rationals
  import RealArith
  import Sequences
  import Limits
  import Measures
  import Rand
  import Uniform
  import Bernoulli
  import Monad
  import Independence
  import Loops
  import BernoulliModel = Bernoulli.Model

  opaque ghost function Sample(gamma: Rationals.Rational): Monad.Hurd<bool>
    requires gamma.denom != 0
    requires gamma.numer >= 0
    decreases gamma.numer
  {
    if gamma.numer <= gamma.denom
    then SampleLe1(gamma)
    else Monad.Bind(
        SampleLe1(Rationals.Int(1)),
        b =>
          var res: Monad.Hurd<bool> :=
            if b
            then Sample(Rationals.Rational(gamma.numer - gamma.denom, gamma.denom))
            else Monad.Return(false);
          res
      )
  }

  ghost function SampleLe1(gamma: Rationals.Rational): Monad.Hurd<bool>
    requires 0 <= gamma.numer <= gamma.denom
  {
    Monad.Map(
      Le1Loop(gamma)((true, 0)),
      (ak: (bool, nat)) => ak.1 % 2 == 1
    )
  }

  opaque ghost function Le1Loop(gamma: Rationals.Rational): ((bool, nat)) -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    Le1LoopTerminatesAlmostSurely(gamma);
    Loops.While(
      Le1LoopCondition,
      Le1LoopIter(gamma)
    )
  }

  ghost function Le1LoopCondition(ak: (bool, nat)): bool {
    ak.0
  }

  ghost function Le1LoopIter(gamma: Rationals.Rational): ((bool, nat)) -> Monad.Hurd<(bool, nat)>
    requires 0 <= gamma.numer <= gamma.denom
  {
    (ak: (bool, nat)) =>
      var k': nat := ak.1 + 1;
      Monad.Map(
        BernoulliModel.Sample(gamma.numer, k' * gamma.denom),
        a => (a, k'))
  }

  lemma {:axiom} Le1LoopIterCorrectness(gamma: Rationals.Rational, ak: (bool, nat), k': nat) // TODO
    requires k' == ak.1 + 1
    requires 0 <= gamma.numer <= gamma.denom
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopIter(gamma)(ak), iset{(true, k')})) == gamma.numer as real / (k' * gamma.denom) as real
    ensures Rand.prob(Monad.BitstreamsWithValueIn(Le1LoopIter(gamma)(ak), iset{(false, k')})) == 1.0 - gamma.numer as real / (k' * gamma.denom) as real

  ghost function Le1LoopDivergenceProbBound(k: nat): nat -> real {
    (fuel: nat) => if fuel == 0 then 1.0 else 1.0 / (k + fuel) as real
  }

  /* Proves that Le1Loop terminates almost surely.
   *
   * It does so by bounding the probability of nontermination (divergence) after `fuel` iterations between 0.0 and `Le1LoopDivergenceProbBound(k)(fuel)`.
   * Since both lower and upper bounds converge to zero as `fuel` tends to infinity, the divergence probability is zero.
   */
  lemma Le1LoopTerminatesAlmostSurely(gamma: Rationals.Rational)
    requires 0 <= gamma.numer <= gamma.denom
    ensures Loops.WhileTerminatesAlmostSurely(Le1LoopCondition, Le1LoopIter(gamma))
  {
    var divergenceLower := Sequences.Constant(0.0);
    forall init: (bool, nat) ensures Loops.WhileTerminatesAlmostSurelyInit(Le1LoopCondition, Le1LoopIter(gamma), init) {
      var divergenceProb := Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), init);
      assert Sequences.IsLeq(divergenceProb, Le1LoopDivergenceProbBound(0)) by {
        forall fuel: nat ensures divergenceProb(fuel) <= Le1LoopDivergenceProbBound(0)(fuel) {
          Le1LoopDivergenceProbabilityBound(gamma, init, fuel);
          assert divergenceProb(fuel) <= Le1LoopDivergenceProbBound(init.1)(fuel) <= Le1LoopDivergenceProbBound(0)(fuel) by {
            if fuel > 0 {
              RealArith.DivisionIsAntiMonotonic(1.0, (fuel + init.1) as real, fuel as real);
            }
          }
        }
      }
      assert Limits.ConvergesTo(Le1LoopDivergenceProbBound(0), 0.0) by {
        assert Sequences.IsSuffixOf(Sequences.OneOverNPlus1, Le1LoopDivergenceProbBound(0), 1);
        Limits.OneOverNPlus1ConvergesToZero();
        Limits.SuffixConvergesToSame(Le1LoopDivergenceProbBound(0), Sequences.OneOverNPlus1, 1, 0.0);
      }
      assert Sequences.IsLeq(divergenceLower, divergenceProb) by {
        forall n: nat ensures divergenceProb(n) >= 0.0 {
          Rand.ProbIsProbabilityMeasure();
          var event := iset s | !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), init, s)(n);
          assume {:axiom} event in Rand.eventSpace; // TODO
          assert Rand.prob(event) >= 0.0;
        }
      }
      assert Limits.ConvergesTo(divergenceLower, 0.0) by {
        Limits.ConstantSequenceConverges(divergenceLower, 0.0);
      }
      assert Limits.ConvergesTo(divergenceProb, 0.0) by {
        Limits.Sandwich(divergenceLower, divergenceProb, Le1LoopDivergenceProbBound(0), 0.0);
      }
      Loops.EnsureWhileTerminatesAlmostSurelyViaLimit(Le1LoopCondition, Le1LoopIter(gamma), init);
    }
  }

  /* Proves a bound on the nontermination (divergence) probability of Le1Loop(gamma)(ak) after `n` iterations.
   *
   * We could prove an even stronger bound of (gamma / (k + 1)) * (gamma / (k + 2)) * ... * (gamma / (k + n)),
   * where k = ak.1.
   * But such a bound is more complicated to express, so we instead prove the upper bound 1 if n = 0 and 1 / (k + n) else.
   *
   * We do this inductively.
   * For n = 0 the bound of 1 is clear.
   * For n >= 1, we reason as follows:
   * If ak.0 is false, the loop stops and the divergence probability is zero.
   * So the interesting case is ak.0 == true.
   * If n == 1, the probability of sampling true from the Bernoulli(gamma / (k + 1)) distribution is <= 1 / (k + 1) == 1 / (k + n).
   * Since the loop exits if we sample false, this is an upper bound on the divergence probability.
   * If n > 1, the probability of divergence is at most that of the remaining n - 1 loop iterations diverging.
   * By induction hypothesis, this is <= 1 / (k' + n - 1) == 1 / (k + n) as desired.
   */
  lemma Le1LoopDivergenceProbabilityBound(gamma: Rationals.Rational, ak: (bool, nat), n: nat)
    requires 0 <= gamma.numer <= gamma.denom
    decreases n
    ensures Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n) <= Le1LoopDivergenceProbBound(ak.1)(n)
  {
    var divergenceEvent := iset s | !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak, s)(n);
    assume {:axiom} divergenceEvent in Rand.eventSpace;
    if n == 0 {
      assert Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n) == Rand.prob(divergenceEvent);
      Rand.ProbIsProbabilityMeasure();
      Measures.ProbabilityLe1(divergenceEvent, Rand.eventSpace, Rand.prob);
      assert Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n) <= Le1LoopDivergenceProbBound(ak.1)(n);
    } else {
      if Le1LoopCondition(ak) {
        var (a, k) := ak;
        var k': nat := k + 1;
        var continueValues := iset ak': (bool, nat) | Le1LoopCondition(ak');
        var firstIterationContinuesEvent := Monad.BitstreamsWithValueIn(Le1LoopIter(gamma)(ak), continueValues);
        var restOfLoopDiverges := iset s | !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), (true, k'), s)(n - 1);
        assume {:axiom} firstIterationContinuesEvent in Rand.eventSpace; // TODO
        assume {:axiom} restOfLoopDiverges in Rand.eventSpace; // TODO
        assert divergenceEvent == firstIterationContinuesEvent * Monad.BitstreamsWithRestIn(Le1LoopIter(gamma)(ak), restOfLoopDiverges) by {
          forall s ensures s in divergenceEvent <==> s in firstIterationContinuesEvent && s in Monad.BitstreamsWithRestIn(Le1LoopIter(gamma)(ak), restOfLoopDiverges) {
            match Le1LoopIter(gamma)(ak)(s)
            case Diverging => {}
            case Result(ak', s') =>
              assert s in firstIterationContinuesEvent <==> ak'.0;
              calc {
                s in divergenceEvent;
                !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak, s)(n);
                { Loops.WhileCutTerminatesWithFuelUnroll(Le1LoopCondition, Le1LoopIter(gamma), ak, s, ak', s', n); }
                !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak', s')(n - 1);
              }
              if ak'.0 {
                assert ak' == (true, k');
                assert s' in restOfLoopDiverges <==> !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak', s')(n - 1);
              } else {
                assert s !in firstIterationContinuesEvent;
                assert s !in divergenceEvent;
              }
          }
        }
        assert Rand.prob(divergenceEvent) == Rand.prob(firstIterationContinuesEvent) * Rand.prob(restOfLoopDiverges) by {
          assume {:axiom} Independence.IsIndepFunction(Le1LoopIter(gamma)(ak)); // TODO
          Independence.ResultsIndependent(Le1LoopIter(gamma)(ak), continueValues, restOfLoopDiverges);
        }
        calc {
          Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n);
          Rand.prob(divergenceEvent);
          Rand.prob(firstIterationContinuesEvent) * Rand.prob(restOfLoopDiverges);
        <= { Le1LoopDivergenceProbabilityBoundHelper(gamma, ak, k', n, firstIterationContinuesEvent, restOfLoopDiverges); }
          Le1LoopDivergenceProbBound(ak.1)(n);
        }
      } else { // i.e. if !LeLoopCondition(ak)
        forall s ensures Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak, s)(n) {}
        assert Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n) == 0.0 by {
          assert iset{} == iset s | !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), ak, s)(n);
          Rand.ProbIsProbabilityMeasure();
        }
      }
      assert Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), ak)(n) <= Le1LoopDivergenceProbBound(ak.1)(n);
    }
  }

  lemma Le1LoopDivergenceProbabilityBoundHelper(gamma: Rationals.Rational, ak: (bool, nat), k': nat, n: nat, firstIterationContinuesEvent: iset<Rand.Bitstream>, restOfLoopDiverges: iset<Rand.Bitstream>)
    requires 0 <= gamma.numer <= gamma.denom
    requires n >= 1
    requires k' == ak.1 + 1
    requires firstIterationContinuesEvent == iset s | Le1LoopIter(gamma)(ak)(s).Satisfies(Le1LoopCondition)
    requires restOfLoopDiverges == iset s | !Loops.WhileCutTerminatesWithFuel(Le1LoopCondition, Le1LoopIter(gamma), (true, k'), s)(n - 1)
    requires firstIterationContinuesEvent in Rand.eventSpace
    requires restOfLoopDiverges in Rand.eventSpace
    decreases n, 1
    ensures Rand.prob(firstIterationContinuesEvent) * Rand.prob(restOfLoopDiverges) <= Le1LoopDivergenceProbBound(ak.1)(n)
  {
    var k := ak.1;
    var k' := k + 1;
    assert 0.0 <= Rand.prob(restOfLoopDiverges) <= 1.0 by {
      Rand.ProbIsProbabilityMeasure();
      Measures.ProbabilityLe1(restOfLoopDiverges, Rand.eventSpace, Rand.prob);
    }
    assert 0.0 <= Rand.prob(firstIterationContinuesEvent) <= 1.0 by {
      Rand.ProbIsProbabilityMeasure(); Measures.ProbabilityLe1(firstIterationContinuesEvent, Rand.eventSpace, Rand.prob);
    }
    if n == 1 {
      assert Rand.prob(firstIterationContinuesEvent) <= 1.0 / k' as real by {
        assert firstIterationContinuesEvent == Monad.BitstreamsWithValueIn(Le1LoopIter(gamma)(ak), iset{(true, k')}) by {
          forall s ensures s in firstIterationContinuesEvent <==> s in Monad.BitstreamsWithValueIn(Le1LoopIter(gamma)(ak), iset{(true, k')}) {}
        }
        calc {
          Rand.prob(firstIterationContinuesEvent);
          { Le1LoopIterCorrectness(gamma, ak, k'); }
          gamma.numer as real / (k' * gamma.denom) as real;
        <=
          1.0 / k' as real;
        }
      }
      calc {
        Rand.prob(firstIterationContinuesEvent) * Rand.prob(restOfLoopDiverges);
      <= { RealArith.MulMonotonic(Rand.prob(firstIterationContinuesEvent), Rand.prob(restOfLoopDiverges), 1.0); }
        Rand.prob(firstIterationContinuesEvent);
      <=
        1.0 / k' as real;
        1.0 / (k + n) as real;
      }
    } else {
      calc {
        Rand.prob(firstIterationContinuesEvent) * Rand.prob(restOfLoopDiverges);
      <= { RealArith.MulMonotonic(Rand.prob(restOfLoopDiverges), Rand.prob(firstIterationContinuesEvent), 1.0); }
        Rand.prob(restOfLoopDiverges);
        Loops.WhileCutDivergenceProbability(Le1LoopCondition, Le1LoopIter(gamma), (true, k'))(n - 1);
      <= { Le1LoopDivergenceProbabilityBound(gamma, (true, k'), n - 1); }
        1.0 / (k + n) as real;
      }
    }
  }

}
