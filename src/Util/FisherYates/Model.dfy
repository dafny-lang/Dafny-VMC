/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Uniform
  import Rand
  import Permutations

  ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): (h: Monad.Hurd<seq<T>>)
    requires i <= |xs|
    decreases |xs| - i
    //  ensures forall s :: h(s).Result? ==> multiset(h(s).value) == multiset(xs)
    ensures forall s :: h(s).Result? ==> |h(s).value| == |xs|
  {
    (s: Rand.Bitstream) =>
      if |xs[i..]| > 1 then
        var (j, s) :- Uniform.Model.IntervalSample(i, |xs|)(s);
        var xs := Permutations.Swap(xs, i, j);
        Shuffle(xs, i + 1)(s)
      else
        Monad.Return(xs)(s)
  }
}