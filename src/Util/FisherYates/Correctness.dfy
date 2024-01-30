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
    requires forall a, b | 0 <= a < b < |xs| :: xs[a] != xs[b]
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
    assert |xs| == |p| by {
      Model.PermutationsPreserveCardinality(xs, p);
    }
    CorrectnessFisherYatesUniqueElementsGeneral(xs, p, 0);
  }

  lemma {:vcs_split_on_every_assert} CorrectnessFisherYatesUniqueElementsGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
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
            { assert |xs[i..]| != 0 ==> [xs[i]] == [p[i]] by { assert |xs[i..]| != 0 ==> assert p[i..] == [p[i]]; assert xs[i..] == [xs[i]]; assert multiset(p[i..]) == multiset(xs[i..]); multiset([p[i]]) == multiset([xs[i]]); } }
            if |xs[i..]| == 0 then true else true;
            true;
          }
        }
      }
      reveal NatArith.FactorialTraditional();
      Rand.ProbIsProbabilityMeasure();
      assert Measures.IsProbability(Rand.eventSpace, Rand.prob);
    } else {
      calc {
        true;
        |xs[i..]| > 1;
        |xs| - i > 1;
        |xs| > i + 1;
      }
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
        assert forall a, b | i+1 <= a < b < |ys| :: ys[a] != ys[b] by {
          forall a, b | i+1 <= a < b < |ys|
            ensures ys[a] != ys[b]
          {
            assume {:axiom} false;
             /* if x == ys[i] {
              calc {
                multiset(ys[i+1..])[x];
                multiset(ys[i..])[x] - multiset([ys[i]])(x);
                multiset(ys[i..])[x] - 1;

              }
            }

            calc {
              1;
            <= { assert x in ys[i+1..]; }
              multiset(ys[i+1..])[x];
            }
            calc {
              multiset(ys[i+1..])[x];
            ==
              (multiset(ys) - multiset(ys[..i]))[x];
            ==
              multiset(ys)[x] - multiset(ys[..i])[x];
            ==
              multiset(xs)[x] - multiset(xs[..i])[x];
            == { }
              1 - multiset(ys[..i])[x];
            <=
              1
            } */
          }
        }
        InductionHypothesisPrecondition1(xs, ys, p, i, j);
        CorrectnessFisherYatesUniqueElementsGeneral(ys, p, i+1);
      }
      assert DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e') by {
        assume {:axiom} false;
      }
      assert Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real) by {
        reveal DecomposeE;
        reveal HIsIndependent;
        reveal InductionHypothesis;
        reveal BitStreamsInA;
        ProbabilityOfE(xs, p, i, j, h, A, e, e');
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

  lemma InductionHypothesisPrecondition1<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat)
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires ys == Model.Swap(xs, i, j)
    requires |xs[i..]| > 1
    ensures multiset(ys[i+1..]) == multiset(p[i+1..])
  {
    if j == i {
      calc {
        multiset(ys[i+1..]);
        { assert ys[i+1..] == xs[i+1..] by { assert xs == ys; } }
        multiset(xs[i+1..]);
        { MultisetOfSequence(xs, i, i+1); }
        multiset(xs[i..]) - multiset(xs[i..i+1]);
        { assert xs[i..i+1] == [xs[i]]; }
        multiset(xs[i..]) - multiset([xs[i]]);
        { assert multiset(xs[i..]) == multiset(p[i..]); assert xs[i] == xs[j] by { assert i == j; } }
        multiset(p[i..]) - multiset([xs[j]]);
        { assert multiset([xs[j]]) == multiset([p[i]]) by { assert xs[j] == p[i]; } }
        multiset(p[i..]) - multiset([p[i]]);
        { assert multiset([p[i]]) == multiset(p[i..i+1]) by { assert [p[i]] == p[i..i+1]; } }
        multiset(p[i..]) - multiset(p[i..i+1]);
        { assert |p| == |xs|; MultisetOfSequence(p, i, i+1); }
        multiset(p[i+1..]);
      }
    } else {
      assert i+1 <= j by {
        assert i <= j;
        assert i != j;
        assert i < j;
      }
      assert |xs| > j;
      assert |xs| == |ys|;
      calc {
        multiset(ys[i+1..]);
        { assert i+1 <= j; assert ys[i+1..] == ys[i+1..j] + ys[j..]; }
        multiset(ys[i+1..j] + ys[j..]);
        { assert ys[j..] == [ys[j]] + ys[j+1..]; }
        multiset(ys[i+1..j] + [ys[j]] + ys[j+1..]);
        { assert ys[i+1..j] == xs[i+1..j];}
        multiset(xs[i+1..j] + [ys[j]] + ys[j+1..]);
        { assert ys[j] == xs[i]; }
        multiset(xs[i+1..j] + [xs[i]] + ys[j+1..]);
        { assert ys[j+1..] == xs[j+1..]; }
        multiset(xs[i+1..j] + [xs[i]] + xs[j+1..]);
        { assert multiset([xs[j]]) - multiset([xs[j]]) == multiset{}; }
        multiset(xs[i+1..j] + [xs[i]] + xs[j+1..]) + multiset([xs[j]]) - multiset([xs[j]]);
        { assert multiset(xs[i+1..j] + [xs[i]] + xs[j+1..]) + multiset([xs[j]]) == multiset(xs[i+1..j] + [xs[i]] + xs[j+1..] + [xs[j]]); }
        multiset(xs[i+1..j] + [xs[i]] + xs[j+1..] + [xs[j]]) - multiset([xs[j]]);
        { assert multiset(xs[i+1..j] + [xs[i]] + xs[j+1..] + [xs[j]]) == multiset(xs[i+1..j]) + multiset([xs[i]]) + multiset(xs[j+1..]) + multiset([xs[j]]); }
        multiset(xs[i+1..j]) + multiset([xs[i]]) + multiset(xs[j+1..]) + multiset([xs[j]]) - multiset([xs[j]]);
        { assert multiset(xs[i+1..j]) + multiset([xs[i]]) + multiset(xs[j+1..]) + multiset([xs[j]]) == multiset([xs[i]]) + multiset(xs[i+1..j]) + multiset([xs[j]]) + multiset(xs[j+1..]); }
        multiset([xs[i]]) + multiset(xs[i+1..j]) + multiset([xs[j]]) + multiset(xs[j+1..]) - multiset([xs[j]]);
        { assert multiset([xs[i]]) + multiset(xs[i+1..j]) + multiset([xs[j]]) + multiset(xs[j+1..]) == multiset([xs[i]] + xs[i+1..j] + [xs[j]] + xs[j+1..]); }
        multiset([xs[i]] + xs[i+1..j] + [xs[j]] + xs[j+1..]) - multiset([xs[j]]);
        { assert [xs[i]] + xs[i+1..j] == xs[i..j]; assert [xs[j]] + xs[j+1..] == xs[j..]; }
        multiset(xs[i..j] + xs[j..]) - multiset([xs[j]]);
        { assert xs[i..j] + xs[j..] == xs[i..]; }
        multiset(xs[i..]) - multiset([xs[j]]);
        { assert multiset(xs[i..]) == multiset(p[i..]); assert xs[j] == p[i]; }
        multiset(p[i..]) - multiset([p[i]]);
        { assert [p[i]] == p[i..i+1]; }
        multiset(p[i..]) - multiset(p[i..i+1]);
        { assert |p| == |xs|; MultisetOfSequence(p, i, i+1); }
        multiset(p[i+1..]);
      }
    }
  }

  lemma ProbabilityOfE<T(!new)>(xs: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>)
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires |xs|-i > 1
    requires DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
    requires HIsIndependent: Independence.IsIndepFunction(h)
    requires InductionHypothesis: e' in Rand.eventSpace && Rand.prob(e') == 1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real)
    requires BitStreamsInA: Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j))
    ensures
      Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real)
  {
    calc {
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
      { assert (NatArith.FactorialTraditional(|xs|-(i+1)) as real) == (NatArith.FactorialTraditional((|xs|-i)-1) as real) by { assert |xs|-(i+1) == (|xs|-i)-1; } }
      (1.0 / ((|xs|-i) as real)) * (1.0 / (NatArith.FactorialTraditional((|xs|-i)-1) as real));
      { assert |xs|-i > 1; RealArith.SimplifyFractionsMultiplication(1.0, (|xs|-i) as real, 1.0, NatArith.FactorialTraditional((|xs|-i)-1) as real); }
      (1.0 * 1.0) / (((|xs|-i) as real) * (NatArith.FactorialTraditional((|xs|-i)-1) as real));
      { assert 1.0 * 1.0 == 1.0; }
      1.0 / (((|xs|-i) as real) * (NatArith.FactorialTraditional((|xs|-i)-1) as real));
      { RealArith.AsRealOfMultiplication(|xs|-i, NatArith.FactorialTraditional((|xs|-i)-1)); }
      1.0 / (((|xs|-i) * NatArith.FactorialTraditional((|xs|-i)-1)) as real);
      { assert (|xs|-i) * NatArith.FactorialTraditional((|xs|-i)-1) == NatArith.FactorialTraditional(|xs|-i) by { reveal NatArith.FactorialTraditional(); } }
      1.0 / (NatArith.FactorialTraditional(|xs|-i) as real);
    }
  }

  lemma MultisetOfSequence<T>(xs: seq<T>, i: nat, j: nat)
    requires i <= j < |xs|
    ensures multiset(xs[i..]) - multiset(xs[i..j]) == multiset(xs[j..])
  {
    calc {
      multiset(xs[i..]) - multiset(xs[i..j]);
      { assert xs[i..] == xs[i..j] + xs[j..]; }
      multiset(xs[i..j] + xs[j..]) - multiset(xs[i..j]);
      { assert  multiset(xs[i..j] + xs[j..]) == multiset(xs[i..j]) + multiset(xs[j..]); }
      multiset(xs[i..j]) + multiset(xs[j..]) - multiset(xs[i..j]);
      multiset(xs[j..]);
    }
  }

}