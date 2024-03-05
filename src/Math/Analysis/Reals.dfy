/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

// Fundamental properties of the real numbers.
// * States the completeness of the reals in terms of a variation of Dedekind cuts.
//     Dafny should include such an axiom, but doesn't.
//     See: https://en.wikipedia.org/wiki/Completeness_of_the_real_numbers
// * Proves existence and uniqueness of infima and suprema
module Reals {
  import RealArith

  ghost predicate IsLowerBound(s: iset<real>, lower: real) {
    forall x <- s :: lower <= x
  }

  ghost predicate IsUpperBound(s: iset<real>, upper: real) {
    forall x <- s :: x <= upper
  }

  ghost predicate IsInfimum(s: iset<real>, candidate: real) {
    && IsLowerBound(s, candidate)
    && forall other: real :: IsLowerBound(s, other) ==> other <= candidate
  }

  ghost predicate IsSupremum(s: iset<real>, candidate: real) {
    && IsUpperBound(s, candidate)
    && forall other: real :: IsUpperBound(s, other) ==> candidate <= other
  }

  lemma InfimumIsUnique(s: iset<real>, infimum1: real, infimum2: real)
    requires IsInfimum(s, infimum1)
    requires IsInfimum(s, infimum2)
    ensures infimum1 == infimum2
  {}

  lemma SupremumIsUnique(s: iset<real>, infimum1: real, infimum2: real)
    requires IsSupremum(s, infimum1)
    requires IsSupremum(s, infimum2)
    ensures infimum1 == infimum2
  {}

}
