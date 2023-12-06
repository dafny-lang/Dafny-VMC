/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module FisherYates.Correctness {
  import Model
  import Permutations
  import Rand

  lemma {:axiom} CorrectnessFisherYates<T>(xs: seq<T>, p: seq<T>)
    requires Permutations.IsPermutationOf(p, xs)
    ensures |Permutations.CalculateAllPermutationsOf(xs)| > 0
    ensures
      var e := iset s | Model.Shuffle(xs)(s).Equals(p);
      && e in Rand.eventSpace
      && Rand.prob(e) == 1.0 / (|Permutations.CalculateAllPermutationsOf(xs)| as real)

}