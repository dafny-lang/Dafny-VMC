/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Uniform
  import Rand

  ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): (h: Monad.Hurd<seq<T>>)
    requires i <= |xs|
    decreases |xs| - i
    ensures forall s :: h(s).Result? ==> multiset(h(s).value) == multiset(xs)
    ensures forall s :: h(s).Result? ==> |h(s).value| == |xs|
  {
    (s: Rand.Bitstream) =>
      if i < |xs| then
        var (j, s) :- Uniform.Model.IntervalSample(i, |xs|)(s);
        var xs := Swap(xs, i, j);
        Shuffle(xs, i + 1)(s)
      else
        Monad.Return(xs)(s)
  }

  function Swap<T>(s: seq<T>, i: nat, j: nat): (t: seq<T>)
    requires i <= j
    requires 0 <= i < |s|
    requires 0 <= j < |s|
    ensures |s| == |t|
  {
    if i == j then
      s
    else
      s[..i] + [s[j]] + s[i+1..j] + [s[i]] + s[j+1..]
  }
}