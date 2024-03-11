/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

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
