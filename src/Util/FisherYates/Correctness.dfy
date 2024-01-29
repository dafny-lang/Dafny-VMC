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

  /*******
   Lemmas
  *******/

  lemma CorrectnessFisherYatesUniqueElements<T(!new)>(xs: seq<T>, p: seq<T>)
    requires forall x | x in xs :: multiset(xs)[x] == 1
    requires multiset(p) == multiset(xs)
    ensures NatArith.Factorial(|xs|) != 0
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.Factorial(|xs|) as real)
  {
    var e := iset s | Model.Shuffle(xs)(s).Equals(p);
    var i := 0;
    var e' := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
    assert e == e';
    CorrectnessFisherYatesUniqueElementsGeneral(xs, p, 0);
  }

  lemma CorrectnessFisherYatesUniqueElementsGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    requires i <= |xs|
    requires i <= |p|
    requires forall x | x in xs[i..] :: multiset(xs[i..])[x] == 1
    requires multiset(p[i..]) == multiset(xs[i..])
    ensures NatArith.Factorial(|xs[i..]|) != 0
    ensures
      var e := iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..];
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NatArith.Factorial(|xs|-i) as real)
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
      reveal NatArith.Factorial();
      Rand.ProbIsProbabilityMeasure();
      assert Measures.IsProbability(Rand.eventSpace, Rand.prob);
    } else {
      assume {:axiom} false;
      var h := Uniform.Model.IntervalSample(i, |xs|);
      assert HIsIndependent: Independence.IsIndep(h) by {
        Uniform.Correctness.IntervalSampleIsIndep(i, |xs|);
      }
      var A := iset j | i <= j < |xs| && xs[j] == p[i];
      assert A != iset{} by {
        assume {:axiom} false;
        //assert Permutations.IsPermutationOf(p[i..], xs[i..]);
      }
      var j :| j in A;
      assert BitStreamsInA: (iset s | s in Monad.BitstreamsWithValueIn(h, A)) == (iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) by {
        assume {:axiom} false;
      }
      var ys := Model.Swap(xs, i, j);
      var e' := iset s | Model.Shuffle(ys, i+1)(s).Result? && Model.Shuffle(ys, i+1)(s).value[i+1..] == p[i+1..];
      assert DecomposeE: e == (iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, e')) by {
        assume {:axiom} false;
      }
      calc {
        Rand.prob(e);
        Rand.prob(iset s | Model.Shuffle(xs, i)(s).Result? && Model.Shuffle(xs, i)(s).value[i..] == p[i..]);
        { reveal DecomposeE; }
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, e'));
        { reveal HIsIndependent; Independence.ResultsIndependent(h, A, e'); }
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) * Rand.prob(e');
        { reveal BitStreamsInA; }
        Rand.prob(iset s | Uniform.Model.IntervalSample(i, |xs|)(s).Equals(j)) * Rand.prob(e');
        { Uniform.Correctness.UniformFullIntervalCorrectness(i, |xs|, j); CorrectnessFisherYatesUniqueElementsGeneral(ys, p, i+1); }
        (1.0 / ((|xs|-i) as real)) * 1.0 / (NatArith.Factorial(|xs|-(i+1)) as real);
        { assert |xs|-(i+1) == |xs|-i-1; }
        (1.0 / ((|xs|-i) as real)) * 1.0 / (NatArith.Factorial((|xs|-i)-1) as real);
        1.0 * 1.0 / ((|xs|-i) as real) * (NatArith.Factorial((|xs|-i)-1) as real);
        1.0 / (((|xs|-i) * NatArith.Factorial((|xs|-i)-1)) as real);
        { assert (|xs|-i) * NatArith.Factorial((|xs|-i)-1) == NatArith.Factorial(|xs|-i); }
        1.0 / (NatArith.Factorial(|xs|-i) as real);
      }
    }
  }

}