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

  /************
   Definitions
  ************/

  ghost function CorrectnessConstructEvent<T(!new)>(xs: seq<T>, p: seq<T>, i: nat): iset<Rand.Bitstream>
    requires i <= |xs|
    requires i <= |p|
  {
    iset s | Model.Shuffle(xs, i)(s).value[i..] == p[i..]
  }

  ghost predicate CorrectnessPredicate<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    requires i <= |xs|
    requires i <= |p|
  {
    var e := CorrectnessConstructEvent(xs, p, i);
    e in Rand.eventSpace
    && Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real)
  }

  /*******
   Lemmas
  *******/

  lemma CorrectnessFisherYates<T(!new)>(xs: seq<T>, p: seq<T>)
    requires
      var xs' := seq(|xs|, i requires 0 <= i < |xs| => (xs[i], i));
      var p' := seq(|p|, i requires 0 <= i < |p| => (p[i], i));
      multiset(p') == multiset(xs')
    ensures
      var xs' := seq(|xs|, i requires 0 <= i < |xs| => (xs[i], i));
      var p' := seq(|p|, i requires 0 <= i < |p| => (p[i], i));
      var e := iset s | Model.Shuffle(xs')(s).Equals(p');
      e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|) as real)
  {
    var xs' := seq(|xs|, i requires 0 <= i < |xs| => (xs[i], i));
    var p' := seq(|p|, i requires 0 <= i < |p| => (p[i], i));
    CorrectnessFisherYatesUniqueElements(xs', p');
  }

  lemma CorrectnessFisherYatesUniqueElements<T(!new)>(xs: seq<T>, p: seq<T>)
    requires forall a, b | 0 <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p) == multiset(xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|) as real)
  {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    var i := 0;
    var e' := iset s | Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    assert e == e';
    assert |xs| == |p| by {
      Model.PermutationsPreserveCardinality(xs, p);
    }
    CorrectnessFisherYatesUniqueElementsGeneral(xs, p, 0);
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    ensures CorrectnessPredicate(xs, p, i)
  {
    var e := iset s | Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    if |xs[i..]| <= 1 {
      CorrectnessFisherYatesUniqueElementsGeneralLeq1(xs, p, i);
    } else {
      CorrectnessFisherYatesUniqueElementsGeneralGreater1(xs, p, i);
    }
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneralLeq1<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires |xs[i..]| <= 1
    ensures CorrectnessPredicate(xs, p, i)
  {
    Model.PermutationsPreserveCardinality(p[i..], xs[i..]);
    var e := iset s | Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    assert e == Measures.SampleSpace() by {
      forall s
        ensures s in e
      {
        calc {
          s in e;
          Model.Shuffle(xs, i)(s).value[i..] == p[i..];
          { assert Model.Shuffle(xs, i)(s) == Monad.Return(xs)(s); }
          Monad.Return(xs)(s).value[i..] == p[i..];
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
    assert CorrectnessPredicate(xs, p, i) by {
      reveal NatArith.FactorialTraditional();
      Rand.ProbIsProbabilityMeasure();
      assert Measures.IsProbability(Rand.eventSpace, Rand.prob);
      assert Measures.SampleSpace() == Measures.Complement<Rand.Bitstream>(iset{});
      calc {
        Rand.prob(e);
        1.0;
        1.0 / 1.0;
        1.0 / (1 as real);
        1.0 / (NatArith.FactorialTraditional(|xs|-i) as real);
      }
    }
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneralGreater1ASingleton<T(!new)>(xs: seq<T>, p: seq<T>, i: nat) returns (j: nat)
    requires i <= |xs|
    requires i <= |p|
    requires |xs| == |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p[i..]) == multiset(xs[i..])
    requires |xs[i..]| > 1
    ensures
      var A := iset j | i <= j < |xs| && xs[j] == p[i];
      A != iset{} && A == iset{j}
  {
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
    j :| j in A;
    assert A == iset{j} by {
      assert forall k :: k in A <==> k in iset{j} by {
        forall k
          ensures k in A <==> k in iset{j}
        {
          if k in A {
            assert xs[k] == p[i];
            assert xs[j] == p[i];
            assert xs[k] == xs[j];
            assert k == j by {
              assert forall a, b | i <= a < b < |xs| :: xs[a] != xs[b];
            }
            assert k in iset{j};
          }
          if k in iset{j} {
            assert k == j;
            assert k in A;
          }
        }
      }
    }
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneralGreater1CorrectnessPredicate<T(!new)>(xs: seq<T>, p: seq<T>, i: nat, j: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires |xs| == |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p[i..]) == multiset(xs[i..])
    requires |xs[i..]| > 1
    requires i <= j < |xs| && xs[j] == p[i]
    ensures
      var ys := Model.Swap(xs, i, j);
      CorrectnessPredicate(ys, p, i+1)
  {
    var ys := Model.Swap(xs, i, j);
    assert multiset(ys[i+1..]) == multiset(p[i+1..]) by {
      InductionHypothesisPrecondition1(xs, ys, p, i, j);
    }
    assert forall a, b | i+1 <= a < b < |ys| :: ys[a] != ys[b] by {
      InductionHypothesisPrecondition2(xs, ys, p, i, j);
    }
    assert i+1 <= |ys| by {
      calc {
        i + 1;
      <
        |xs|;
      ==
        |ys|;
      }
    }
    assert i < |p| by {
      calc {
        i;
      <
        i+1;
      <
        |xs|;
      ==
        |p|;
      }
    }
    assert |ys| == |p| by {
      calc {
        |ys|;
        |xs|;
        |p|;
      }
    }
    if |ys[i+1..]| > 1 {
      CorrectnessFisherYatesUniqueElementsGeneralGreater1(ys, p, i+1);
    } else {
      CorrectnessFisherYatesUniqueElementsGeneralLeq1(ys, p, i+1);
    }
  }

  lemma {:vcs_split_on_every_assert} CorrectnessFisherYatesUniqueElementsGeneralGreater1<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires |xs[i..]| > 1
    ensures CorrectnessPredicate(xs, p, i)
  {
    Model.PermutationsPreserveCardinality(p[i..], xs[i..]);
    var e := CorrectnessConstructEvent(xs, p, i);
    assert |xs| > i + 1;
    var h := Uniform.Model.IntervalSample(i, |xs|);
    assert Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => h(s).rest) by {
      Uniform.Correctness.IntervalSampleIsMeasurePreserving(i, |xs|);
    }
    assert Independence.IsIndepFunction(h) by {
      Uniform.Correctness.IntervalSampleIsIndepFunction(i, |xs|);
    }
    var A := iset j | i <= j < |xs| && xs[j] == p[i];
    var j := CorrectnessFisherYatesUniqueElementsGeneralGreater1ASingleton(xs, p, i);
    assert A == iset{j};
    assert Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) by {
      BitStreamsInA(xs, p, i, j, h, A);
    }
    var ys := Model.Swap(xs, i, j);
    var e' := CorrectnessConstructEvent(ys, p, i+1);
    assert CorrectnessPredicate(ys, p, i+1) by {
      CorrectnessFisherYatesUniqueElementsGeneralGreater1CorrectnessPredicate(xs, p, i, j);
    }
    assert e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e') by {
      DecomposeE(xs, ys, p, i, j, h, A, e, e');
    }
    assert CorrectnessPredicate(xs, p, i) by {
      CorrectnessFisherYatesUniqueElementsGeneralGreater1Helper(xs, ys, p, i, j, h, A, e, e');
    }
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneralGreater1Helper<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>)
    decreases |xs| - i
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires |xs[i..]| > 1
    requires i <= j < |xs| && xs[j] == p[i]
    requires |xs| == |ys|
    requires ys == Model.Swap(xs, i, j)
    requires e == CorrectnessConstructEvent(xs, p, i)
    requires e' == CorrectnessConstructEvent(ys, p, i+1)
    requires DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
    requires HIsIndependent: Independence.IsIndepFunction(h)
    requires BitStreamsInA: Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j))
    requires InductionHypothesis: CorrectnessPredicate(ys, p, i+1)
    requires hIsMeasurePreserving: Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => h(s).rest)
    ensures CorrectnessPredicate(xs, p, i)
  {
    reveal DecomposeE;
    reveal HIsIndependent;
    reveal BitStreamsInA;
    assert e' in Rand.eventSpace && Rand.prob(e') == 1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real) by {
      assert e' in Rand.eventSpace by {
        assert CorrectnessPredicate(ys, p, i+1) by { reveal InductionHypothesis; }
        assert e' == CorrectnessConstructEvent(ys, p, i+1);
      }
      calc {
        Rand.prob(e');
        { assert CorrectnessPredicate(ys, p, i+1) by { reveal InductionHypothesis; }
          assert e' == CorrectnessConstructEvent(ys, p, i+1); }
        1.0 / (NatArith.FactorialTraditional(|ys|-(i+1)) as real);
        { assert |xs| == |ys|;
          assert |ys|-(i+1) == |xs|-(i+1);
          assert NatArith.FactorialTraditional(|ys|-(i+1)) == NatArith.FactorialTraditional(|xs|-(i+1));
          assert (NatArith.FactorialTraditional(|ys|-(i+1)) as real) == (NatArith.FactorialTraditional(|xs|-(i+1)) as real); }
        1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real);
      }
    }
    reveal hIsMeasurePreserving;
    assert e in Rand.eventSpace by {
      EInEventSpace(xs, p, h, A, e, e');
    }
    assert Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real) by {
      ProbabilityOfE(xs, ys, p, i, j, h, A, e, e');
    }
  }


  lemma BitStreamsInA<T(!new)>(xs: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>)
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires |xs|-i > 1
    requires i <= j < |xs| && xs[j] == p[i]
    requires A == iset j | i <= j < |xs| && xs[j] == p[i]
    requires A == iset{j}
    requires h == Uniform.Model.IntervalSample(i, |xs|)
    ensures Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j))
  {
    assert forall s :: s in Monad.BitstreamsWithValueIn(h, A) <==> s in (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) by {
      forall s
        ensures s in Monad.BitstreamsWithValueIn(h, A) <==> s in (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j))
      {
        if s in Monad.BitstreamsWithValueIn(h, A) {
          assert Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j);
        }
        if s in (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) {
        }
      }
    }
  }

  lemma {:vcs_split_on_every_assert} DecomposeEImplicationOne<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>, s: Rand.Bitstream)
    requires i <= |p|
    requires |xs| == |p|
    requires |xs|-i > 1
    requires i <= |xs|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires A == iset j | i <= j < |xs| && xs[j] == p[i]
    requires A == iset{j}
    requires h == Uniform.Model.IntervalSample(i, |xs|)
    requires ys == Model.Swap(xs, i, j)
    requires e == CorrectnessConstructEvent(xs, p, i)
    requires e' == CorrectnessConstructEvent(ys, p, i+1)
    requires s in e
    ensures s in Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
  {
    var zs := Model.Shuffle(xs, i)(s).value;
    assert zs[i..] == p[i..];
    var k := Uniform.Model.IntervalSample(i, |xs|)(s).value;
    Uniform.Correctness.IntervalSampleBound(i, |xs|, s);
    var s' := Uniform.Model.IntervalSample(i, |xs|)(s).rest;
    assert s in Monad.BitstreamsWithValueIn(h, A) by {
      var ys' := Model.Swap(xs, i, k);
      var zs' := Model.Shuffle(ys', i+1)(s').value;
      assert zs == zs';
      calc {
        p[i];
        zs[i];
        zs'[i];
        { assert Model.ShuffleInvariancePredicatePointwise(ys', Model.Shuffle(ys', i+1)(s'), i); }
        ys'[i];
        xs[k];
      }
      assert k in A;
    }
    assert s in Monad.BitstreamsWithRestIn(h, e') by {
      calc {
        Model.Shuffle(ys, i+1)(s').value[i+1..];
        Model.ShuffleCurried(ys, s', i+1).value[i+1..];
        Model.ShuffleCurried(xs, s, i).value[i+1..];
        Model.Shuffle(xs, i)(s).value[i+1..];
        { assert Model.Shuffle(xs, i)(s).value[i..] == p[i..]; }
        p[i+1..];
      }
    }
    assert s in Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e');
  }

  lemma DecomposeEImplicationTwo<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>, s: Rand.Bitstream)
    requires i <= |p|
    requires |xs| == |p|
    requires |xs|-i > 1
    requires i <= |xs|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires A == iset j | i <= j < |xs| && xs[j] == p[i]
    requires A == iset{j}
    requires h == Uniform.Model.IntervalSample(i, |xs|)
    requires ys == Model.Swap(xs, i, j)
    requires e == CorrectnessConstructEvent(xs, p, i)
    requires e' == CorrectnessConstructEvent(ys, p, i+1)
    requires s in Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
    ensures s in e
  {
    var k := Uniform.Model.IntervalSample(i, |xs|)(s).value;
    assert k in A;
    assert k == j;
    var s' := Uniform.Model.IntervalSample(i, |xs|)(s).rest;
    assert s' in e';
    var ys' := Model.Swap(xs, i, k);
    assert ys' == ys;
    var zs' := Model.Shuffle(ys', i+1)(s').value;
    assert Model.Shuffle(xs, i)(s).value[i..] == p[i..] by {
      calc {
        Model.Shuffle(xs, i)(s).value[i..];
        { assert Model.Shuffle(xs, i)(s).value == zs'; }
        zs'[i..];
        Model.Shuffle(ys', i+1)(s').value[i..];
        { assert ys' == ys; }
        Model.Shuffle(ys, i+1)(s').value[i..];
        { SliceOfSequences(Model.Shuffle(ys, i+1)(s').value, i); }
        [Model.Shuffle(ys, i+1)(s').value[i]] + Model.Shuffle(ys, i+1)(s').value[i+1..];
        { assert Model.ShuffleInvariancePredicatePointwise(ys, Model.Shuffle(ys, i+1)(s'), i); assert Model.Shuffle(ys, i+1)(s').value[i] == ys[i]; }
        [ys[i]] + Model.Shuffle(ys, i+1)(s').value[i+1..];
        { assert ys[i] == xs[k]; }
        [xs[k]] + Model.Shuffle(ys, i+1)(s').value[i+1..];
        { assert xs[k] == p[i]; }
        [p[i]] + p[i+1..];
        { SliceOfSequences(p, i); }
        p[i..];
      }
    }
  }

  lemma DecomposeE<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>)
    requires i <= |p|
    requires |xs| == |p|
    requires |xs|-i > 1
    requires i <= |xs|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires A == iset j | i <= j < |xs| && xs[j] == p[i]
    requires A == iset{j}
    requires h == Uniform.Model.IntervalSample(i, |xs|)
    requires ys == Model.Swap(xs, i, j)
    requires e == CorrectnessConstructEvent(xs, p, i)
    requires e' == CorrectnessConstructEvent(ys, p, i+1)
    ensures
      e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
  {
    assert e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e') by {
      forall s
        ensures s in e <==> s in Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
      {
        if s in e {
          DecomposeEImplicationOne(xs, ys, p, i, j, h, A, e, e', s);
        }
        if s in Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e') {
          DecomposeEImplicationTwo(xs, ys, p, i, j, h, A, e, e', s);
        }
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
      calc {
        multiset(ys[i+1..]);
        { assert i+1 <= j; SliceOfSequencesVariation(ys, i+1, j); }
        multiset(ys[i+1..j] + ys[j..]);
        { SliceOfSequences(ys, j); }
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
        { SliceOfSequencesGeneral(xs, i, j); SliceOfSequences(xs, j); }
        multiset(xs[i..j] + xs[j..]) - multiset([xs[j]]);
        { SliceOfSequencesVariation(xs, i, j); }
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

  lemma InductionHypothesisPrecondition2<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat)
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires ys == Model.Swap(xs, i, j)
    requires |xs[i..]| > 1
    ensures forall a, b | i+1 <= a < b < |ys| :: ys[a] != ys[b]
  {
    assert forall a, b | i+1 <= a < b < |ys| :: ys[a] != ys[b] by {
      forall a, b | i+1 <= a < b < |ys|
        ensures ys[a] != ys[b]
      {
        if a == i+1 {
        }
      }
    }
  }

  lemma EInEventSpace<T(!new)>(xs: seq<T>, p: seq<T>, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>)
    requires |xs| == |p|
    requires DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
    requires InductionHypothesis: e' in Rand.eventSpace
    requires HIsIndependent: Independence.IsIndepFunction(h)
    ensures e in Rand.eventSpace
  {
    reveal InductionHypothesis;
    reveal HIsIndependent;
    assert Independence.IsIndepFunctionCondition(h, A, e');
    assert Monad.BitstreamsWithValueIn(h, A) in Rand.eventSpace;
    assert Monad.BitstreamsWithRestIn(h, e') in Rand.eventSpace;
    Rand.ProbIsProbabilityMeasure();
    Measures.BinaryIntersectionIsMeasurable(Rand.eventSpace, Monad.BitstreamsWithValueIn(h, A), Monad.BitstreamsWithRestIn(h, e'));
    reveal DecomposeE;
  }

  lemma {:vcs_split_on_every_assert} ProbabilityOfE<T(!new)>(xs: seq<T>, ys: seq<T>, p: seq<T>, i: nat, j: nat, h: Monad.Hurd<int>, A: iset<int>, e: iset<Rand.Bitstream>, e': iset<Rand.Bitstream>)
    requires i <= |xs|
    requires i <= |p|
    requires forall a, b | i <= a < b < |xs| :: xs[a] != xs[b]
    requires |xs| == |p|
    requires multiset(p[i..]) == multiset(xs[i..])
    requires i <= j < |xs| && xs[j] == p[i]
    requires ys == Model.Swap(xs, i, j)
    requires |xs|-i > 1
    requires e' in Rand.eventSpace
    requires |xs| == |ys|
    requires DecomposeE: e == Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e')
    requires HIsIndependent: Independence.IsIndepFunction(h)
    requires hIsMeasurePreserving: Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => h(s).rest)
    requires InductionHypothesis: Rand.prob(e') == 1.0 / (NatArith.FactorialTraditional(|xs|-(i+1)) as real)
    requires BitStreamsInA: Monad.BitstreamsWithValueIn(h, A) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j))
    ensures
      Rand.prob(e) == 1.0 / (NatArith.FactorialTraditional(|xs|-i) as real)
  {
    calc {
      Rand.prob(e);
      { reveal DecomposeE; }
      Rand.prob(Monad.BitstreamsWithValueIn(h, A) * Monad.BitstreamsWithRestIn(h, e'));
      { reveal HIsIndependent; reveal InductionHypothesis; reveal hIsMeasurePreserving; Independence.ResultsIndependent(h, A, e'); }
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

  lemma SliceOfSequences<T>(xs: seq<T>, i: nat)
    requires 0 <= i < |xs|
    ensures xs[i..] == [xs[i]] + xs[i+1..]
  {}

  lemma SliceOfSequencesGeneral<T>(xs: seq<T>, i: nat, j: nat)
    requires 0 <= i < j < |xs|
    ensures xs[i..j] == [xs[i]] + xs[i+1..j]
  {}

  lemma SliceOfSequencesVariation<T>(xs: seq<T>, i: nat, j: nat)
    requires 0 <= i <= j < |xs|
    ensures xs[i..] == xs[i..j] + xs[j..]
  {}

}