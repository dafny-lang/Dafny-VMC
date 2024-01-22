/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Permutations
  import Uniform
  import Rand

  opaque ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): Monad.Hurd<seq<T>>
    requires i <= |xs|
    decreases |xs| - i
  {
    (s: Rand.Bitstream) => 
      if i < |xs| then
        var (j, s) :- Uniform.Model.IntervalSample(i, |xs|)(s);
        var xs := Permutations.Swap(xs, i, j);
        Shuffle(xs, i + 1)(s)
      else 
        Monad.Return(xs)(s)
  }
}