/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Model
  import Permutations
  import Rand

  lemma {:axiom} CorrectnessFisherYatesOne<T>(xs: seq<T>, s: Rand.Bitstream)
    ensures
      var r := Model.Shuffle(xs)(s);
      && r.Result?
      && Permutations.IsPermutationOf(xs, r.value)

  lemma {:axiom} CorrectnessFisherTwo<T>(xs: seq<T>, p: seq<T>)
    requires Permutations.IsPermutationOf(p, xs)
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && |Permutations.CalculateAllPermutationsOf(xs)| > 0
      && Rand.prob(e) == 1.0 / (|Permutations.CalculateAllPermutationsOf(xs)| as real)

}