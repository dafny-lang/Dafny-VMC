/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Uniform
  import Rand

  /************
   Definitions
  ************/

  ghost predicate ShuffleInvariancePredicatePointwise<T>(xs: seq<T>, r: Monad.Result<seq<T>>, j: int)
    requires 0 <= j < |xs|
  {
    r.Result? ==> |r.value| == |xs| && r.value[j] == xs[j]
  }

  ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): (h: Monad.Hurd<seq<T>>)
    requires i <= |xs|
    ensures forall s :: h(s).Result? ==> multiset(h(s).value) == multiset(xs) && |h(s).value| == |xs|
    ensures forall s, j | 0 <= j < i :: ShuffleInvariancePredicatePointwise(xs, h(s), j)
  {
    (s: Rand.Bitstream) => ShuffleCurried(xs, s, i)
  }

  ghost function ShuffleCurried<T>(xs: seq<T>, s: Rand.Bitstream, i: nat := 0): (r: Monad.Result<seq<T>>)
    requires i <= |xs|
    decreases |xs| - i
    ensures r.Result? ==> multiset(r.value) == multiset(xs) && |r.value| == |xs|
    ensures forall j | 0 <= j < i :: ShuffleInvariancePredicatePointwise(xs, r, j)
  {
    if |xs| - i > 1 then
      var (j, s') :- Uniform.Model.IntervalSample(i, |xs|)(s);
      assert i <= j < |xs| by { Uniform.Model.IntervalSampleBound(i, |xs|, s); }
      var ys := Swap(xs, i, j);
      var r := ShuffleCurried(ys, s', i + 1);
      assert forall j | 0 <= j < i :: ShuffleInvariancePredicatePointwise(xs, r, j) by {
        forall j | 0 <= j < i 
          ensures ShuffleInvariancePredicatePointwise(xs, r, j) 
        {
          assert ShuffleInvariancePredicatePointwise(ys, r, j);
        }
      }
      r
    else
      Monad.Return(xs)(s)
  }

  function Swap<T>(s: seq<T>, i: nat, j: nat): (t: seq<T>)
    requires i <= j
    requires 0 <= i < |s|
    requires 0 <= j < |s|
    ensures multiset(s) == multiset(t)
    ensures |s| == |t|
    ensures t[..i] == s[..i]
    ensures t[j] == s[i]
    ensures i+1 <= j ==> t[i+1..j] == s[i+1..j]
  {
    if i == j then
      s
    else
      var t := s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..];
      calc {
        multiset(t);
        multiset(s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]);
        multiset(s[..i]) + multiset([s[j]]) + multiset(s[i+1..j]) + multiset([s[i]]) + multiset(s[j+1..]);
        multiset(s[..i]) +  multiset([s[i]]) + multiset(s[i+1..j]) + multiset([s[j]]) + multiset(s[j+1..]);
        multiset(s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..]);
        { assert s[..i] + [s[i]] + s[i+1..j] + [s[j]] + s[j+1..] == s; }
        multiset(s);
      }
      PermutationsPreserveCardinality(t, s);
      t
  }

  /*******
   Lemmas
  *******/

  lemma MultisetAndSequenceCardinality<T>(s: seq<T>)
    ensures |multiset(s)| == |s|
  {}

  lemma PermutationsPreserveCardinality<T>(p: seq<T>, s: seq<T>)
    requires R: multiset(p) == multiset(s)
    ensures |p| == |s|
  {
    calc {
      |p|;
      { MultisetAndSequenceCardinality(p); }
      |multiset(p)|;
      { assert multiset(p) == multiset(s) by { reveal R; }}
      |multiset(s)|;
      { MultisetAndSequenceCardinality(s); }
      |s|;
    }
  }


}