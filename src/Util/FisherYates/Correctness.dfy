/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import NatArith
  import Model
  import Rand
  import Measures
  import Monad
  import Uniform
  import Independence
  import RealArith

  /*******
   Lemmas
  *******/

  lemma CorrectnessFisherYatesUniqueElements<T(!new)>(xs: seq<T>, p: seq<T>)
    requires forall x | x in xs :: multiset(xs)[x] == 1
    requires multiset(p) == multiset(xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|) as real)
  {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    var i := 0;
    var e' := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    assert e == e';
    CorrectnessFisherYatesUniqueElementsGeneral(xs, p, 0);
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall x | x in xs[i..] :: multiset(xs[i..])[x] == 1
    requires multiset(p[i..]) == multiset(xs[i..])
    ensures
      var e := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real)
  {
    Model.PermutationsPreserveCardinality(p[i..], xs[i..]);
    var e := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    if |xs[i..]| <= 1 {
      assert e == Measures.SampleSpace() by {
        forall s
          ensures s in e
        {
          calc {
            s in e;
            Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
            { assert Model.Shuffle(xs, i)(s) == Monad.Return(xs)(s); }
            Monad.Return(xs)(s).Result? && Monad.Return(xs)(s).value[i..] == p[i..];
            { assert Monad.Return(xs)(s).value == xs; }
            xs[i..] == p[i..];
            if |xs[i..]| == 0 then [] == p[i..] else [xs[i]] == p[i..];
            { assert if |xs[i..]| == 0 then p[i..] == [] else p[i..] == [p[i]]; }
            if |xs[i..]| == 0 then true else [xs[i]] == [p[i]];
            { assert multiset(p[i..]) == multiset(xs[i..]); }
            true;
          }
        }
      }
      reveal NatArith.FactorialTraditional();
      Rand.ProbIsProbabilityMeasure();
      assert Measures.IsProbability(Rand.eventSpace, Rand.prob);
    } else {
      var h := Uniform.Model.IntervalSample(i, |xs|);
      assert HIsIndependent: Independence.IsIndepFunction(h) by {
        Uniform.Correctness.IntervalSampleIsIndep(i, |xs|);
        Independence.IsIndepImpliesIsIndepFunction(h);
      }
      var A := iset j | i <= j < |xs| && xs[j] == p[i];
      assert A != iset{} by {
        calc {
          true;
          p[i] in multiset(p[i..]);
          { assert multiset(p[i..]) == multiset(xs[i..]); }
          p[i] in multiset(xs[i..]);
          p[i] in xs[i..];
          exists j | 0 <= j < |xs[i..]| :: xs[i..][j] == p[i];
          exists j | i <= j < |xs| :: xs[j] == p[i];
          { assert forall j :: j in A <==> i <= j < |xs| && xs[j] == p[i]; }
          exists j :: j in A;
        }
      }
      var j :| j in A;
      assert BitStreamsInA: Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) by {
        assume {:axiom} false;
      }
      var ys := Model.Swap(xs, i, j);
      var e' := iset s | Model.Shuffle(ys, i+1)(s).Result? && Model.Shuffle(ys, i+1)(s).value[i+1..] == p[i+1..];
      assert InductionHypothesis: e' in Rand.eventSpace && Rand.prob(e') == 1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real) by {
        assert forall x | x in ys[i+1..] :: multiset(ys[i+1..])[x] == 1 by {
          forall x | x in ys[i+1..]
            ensures multiset(ys[i+1..])[x] == 1
          {
            calc {
              1;
            <= { assert x in ys[i+1..]; }
              multiset(ys[i+1..])[x];
            }
            calc {
              multiset(ys[i+1..])[x];
            <= { assert multiset(ys[i+1..]) <= multiset(ys[i..]); }
              multiset(ys[i..])[x];
            == { assert multiset(ys[i..]) == multiset(xs[i..]); }
              multiset(xs[i..])[x];
            == 
              1;
            }
          }
        }
        CorrectnessFisherYatesUniqueElementsGeneral(ys, p, i+1);
      }
      assert DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e') by {
        assume {:axiom} false;
      }
      assert Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real) by {
/*         calc {
          Rand.prob(e);
          { reveal DecomposeE; }
          Rand.prob(Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e'));
          { reveal HIsIndependent; reveal InductionHypothesis; Independence.ResultsIndependent(h, A, e'); }
          Rand.prob(Monad.BitstreamsWithValueIn(h, A)) * Rand.prob(e');
          { assert Rand.prob(Monad.BitstreamsWithValueIn(h, A)) == Rand.prob(iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) by { reveal BitStreamsInA; } }
          Rand.prob(iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) * Rand.prob(e');
          { assert Rand.prob(iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) ==  (1.0 / ((|xs|-i) as real)) by { Uniform.Correctness.UniformFullIntervalCorrectness(i, |xs|, j); } }
          (1.0 / ((|xs|-i) as real)) * Rand.prob(e');
          { assert Rand.prob(e') == (1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real)) by { reveal InductionHypothesis; } }
          (1.0 / ((|xs|-i) as real)) * (1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real));
          { assert |xs|-(i+1) == |xs|-i-1; }
          (1.0 / ((|xs|-i) as real)) * (1.0 / (NatArith.FactorialTraditional((|xs|-i)-1) as real));
          //{ RealArith.SimplifyFractionsMultiplication(1.0, (|xs|-i) as real, 1.0, NatArith.Factorial((|xs|-i)-1) as real); }
          { assume {:axiom} false; }
          (1.0 * 1.0) / (((|xs|-i) as real) * (NatArith.FactorialTraditional((|xs|-i)-1) as real));
          { assume {:axiom} false; assert 1.0 * 1.0 == 1.0; assert ((|xs|-i) as real) * (NatArith.FactorialTraditional((|xs|-i)-1) as real) == ((|xs|-i) * NatArith.FactorialTraditional((|xs|-i)-1)) as real; }
          1.0 / (((|xs|-i) * NatArith.FactorialTraditional((|xs|-i)-1)) as real);
          { assume {:axiom} false; assert (|xs|-i) * NatArith.FactorialTraditional((|xs|-i)-1) == NatArith.FactorialTraditional(|xs|-i) by { reveal NatArith.FactorialTraditional(); } }
          1.0 / (NatArith.FactorialTraditional(|xs|-i) as real);
        } */
        assume {:axiom} false;
      }
      assert e in Rand.eventSpace by {
        assume {:axiom} false;
  /*       reveal DecomposeE;
        reveal HIsIndependent;
        reveal InductionHypothesis;
        assert Independence.IsIndepFunctionCondition(h, A, e');
        assert Monad.BitstreamsWithValueIn(h, A) in Rand.eventSpace;
        assert Monad.BitstreamsWithRestIn(h, e') in Rand.eventSpace;
        Measures.BinaryUnionIsMeasurable(Rand.eventSpace, Monad.BitstreamsWithValueIn(h, A), Monad.BitstreamsWithRestIn(h, e')); */
      }
    }
  }

}