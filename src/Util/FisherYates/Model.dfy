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
    ensures forall s :: h(s).Result? ==> Permutations.IsPermutationOf(h(s).value, xs)
  {
    (s: Rand.Bitstream) =>
      if |xs[i..]| > 1 then
        var (j, s) :- Uniform.Model.IntervalSample(i, |xs|)(s);
        var ys := Permutations.Swap(xs, i, j);
        assert Permutations.IsPermutationOf(ys, xs);
        Shuffle(ys, i + 1)(s)
      else
        Monad.Return(xs)(s)
  }
}