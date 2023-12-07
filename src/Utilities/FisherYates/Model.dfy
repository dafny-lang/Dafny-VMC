/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Model {
  import Monad
  import Rand
  import Permutations
  import Uniform
  import Loops

  ghost function Shuffle<T>(xs: seq<T>, i: nat := 0): (f: Monad.Hurd<seq<T>>) 
    requires 0 <= i <= |xs|
  {
    assume {:axiom} false; // assume termination
    if i == |xs| then
      Monad.Return(xs)
    else 
      Monad.Bind(
        Uniform.Model.IntervalSample(i, |xs|),
        (j: nat) requires i <= j < |xs| => 
          var ys := Permutations.Swap(xs, i, j);
          Shuffle(ys, i + 1)
      )
  }
  // TODO: add correct version
/*   function Shuffle<T>(xs: seq<T>): (f: Monad.Hurd<seq<T>>) {
    Monad.Map(
      Loops.While(ShuffleWhileLoopCondition, ShuffleWhileLoopBody)((xs, 0)), 
      (x: (seq<T>, nat)) => x.0
    )
  }

  function ShuffleWhileLoopCondition<T>(x: (seq<T>, nat)): bool {
    x.1 < |x.0|
  }

  function ShuffleWhileLoopBody<T>(x: (seq<T>, nat)): Monad.Hurd<(seq<T>, nat)> {
    Monad.Bind(
      Uniform.Model.IntervalSample(x.1, |x.0|),
      (j: nat) => 
        var ys := Permutations.Swap(x.0, 0, j); 
        Monad.Return((ys, x.1 + 1))
    )
  } */

/*   ghost function ShuffleTailRecursive<T>(xs: seq<T>): Monad.Hurd<seq<T>> 
    decreases |xs|
  {
    if |xs| == 0 then 
      Monad.Return(xs)
    else 
      Monad.Bind(
        Uniform.Model.Sample(|xs|),
        (j: nat) requires 0 <= j < |xs| => 
          var ys := Permutations.Swap(xs, 0, j);          
          Monad.Map(ShuffleTailRecursive(ys[1..]), (zs: seq<T>) => [ys[0]] + zs)
          // ShuffleTailRecursiveCurried(ShuffleTailRecursiveCurried(Permutations.Substitute(xs[1..], j-1, xs[0])).Map((zs: set<T>) => [xs[j]] + zs))
      )
  } */

}