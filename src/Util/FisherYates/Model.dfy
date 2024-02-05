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

  ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): (h: Monad.Hurd<seq<T>>)
    requires i <= |xs|
    decreases |xs| - i
    ensures forall s :: h(s).Result? ==> multiset(h(s).value) == multiset(xs) && |h(s).value| == |xs|
    ensures forall s, j | 0 <= j < i :: h(s).Result? ==> h(s).value[j] == xs[j]
  {
    (s: Rand.Bitstream) =>
      if |xs[i..]| > 1 then
        var (j, s') :- Uniform.Model.IntervalSample(i, |xs|)(s);
        assert i <= j < |xs| by { Uniform.Model.IntervalSampleBound(i, |xs|, s); }
        var ys := Swap(xs, i, j);
        Shuffle(ys, i + 1)(s')
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