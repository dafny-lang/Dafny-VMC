/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Model
  import Rand
  import Uniform
  import Monad
  import Independence
  import RealArith

  /************
   Definitions
  ************/

  // Number of permutations of s[i..] == [s[i], s[i+1], ..., s[|s|-1]]
  function NumberOfPermutationsOf<T(==)>(s: seq<T>, i: nat := 0): (n: nat)
    requires |s| != 0 ==> i <= |s| - 1
    decreases |s| - i
    ensures n != 0
  {
    if |s| == 0 || i == |s| - 1 then
      1
    else
      var multiplicity := multiset(s[i..])[s[i]];
      var length := |s[i..]|;
      (length / multiplicity) * NumberOfPermutationsOf(s, i+1)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} CorrectnessMultiset<T>(xs: seq<T>, x: T, i: nat := 0)
    requires i < |xs|
    requires x in xs[i..]
    ensures 
      var A := iset j | i <= j < |xs| && xs[j] == x;
      var e := Monad.BitstreamsWithValueIn(Uniform.Model.IntervalSample(i, |xs|), A);
      var multiplicity := multiset(xs[i..])[x];
      var length := |xs[i..]|;
      && e in Rand.eventSpace
      && Rand.prob(e) == (multiplicity as real) / (length as real)

  lemma CorrectnessFisherYates<T(!new)>(xs: seq<T>, p: seq<T>)
    requires multiset(p) == multiset(xs)
    requires |p| == |xs|
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NumberOfPermutationsOf(xs) as real)
    {
      CorrectnessFisherYatesGeneral(xs, p, 0);
    }

  lemma CorrectnessFisherYatesGeneral<T(!new)>(xs: seq<T>, p: seq<T>, i: nat)
    requires i <= |xs|
    requires multiset(p) == multiset(xs)
    requires |p| == |xs|
    decreases |xs| - i
    ensures
      var e := iset s | Model.Shuffle(xs, i)(s).Map(ys => ys[i..]).Equals(p[i..]);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (NumberOfPermutationsOf(xs, i) as real)
  {
    var e := iset s | Model.Shuffle(xs, i)(s).Map(ys => ys[i..]).Equals(p[i..]);
    if |xs| == 0 {
      assert e == iset s | true;
      assert NumberOfPermutationsOf(xs, i) == 1;
    } else {
      assume {:axiom} false;
      var h := Uniform.Model.IntervalSample(i, |xs|);
      assert Independence.IsIndep(h) by {
        Uniform.Correctness.IntervalSampleIsIndep(i, |xs|);
      }
      var multiplicity := multiset(xs[i..])[p[i]];
      var length := |xs[i..]|;
      var A := iset j | i <= j < |xs| && xs[j] == p[i];
      var j :| j in A;
      var ys := Model.Swap(xs, i, j);
      var E := iset s | Model.Shuffle(ys, i+1)(s).Map(ys => ys[i+1..]).Equals(p[i+1..]);

      calc {
        Rand.prob(e);
        Rand.prob(iset s | Model.Shuffle(xs, i)(s).Map(ys => ys[i..]).Equals(p[i..]));
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A) && s in Monad.BitstreamsWithRestIn(h, E));
        Rand.prob(iset s | s in Monad.BitstreamsWithValueIn(h, A)) * Rand.prob(E);
        { CorrectnessMultiset(xs, p[i], i); CorrectnessFisherYatesGeneral(ys, p, i+1); }
        (multiplicity as real / length as real) * (1.0 / (NumberOfPermutationsOf(xs, i+1) as real));
        (1.0 / ((length as real) / (multiplicity as real))) *  (1.0 / (NumberOfPermutationsOf(xs, i+1) as real));
        (1.0 / ((length / multiplicity) as real)) *  (1.0 / (NumberOfPermutationsOf(xs, i+1) as real));
        { assert 1.0 * 1.0 == 1.0; assert ((length / multiplicity) as real) * (NumberOfPermutationsOf(xs, i+1) as real) == ((length / multiplicity) * NumberOfPermutationsOf(xs, i+1)) as real; }
        1.0 / ((length / multiplicity) * NumberOfPermutationsOf(xs, i+1)) as real;
        1.0 / (NumberOfPermutationsOf(xs, i) as real);
      }
    }
  }

}