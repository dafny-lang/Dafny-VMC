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

  lemma {:axiom} DedekindCompleteness(lower: iset<real>, upper: iset<real>) returns (between: real)
    requires lower != iset{}
    requires upper != iset{}
    requires forall x <- lower, y <- upper :: x <= y
    ensures IsUpperBound(lower, between)
    ensures IsLowerBound(upper, between)

  lemma Completeness(lower: iset<real>, upper: iset<real>)
    requires lower != iset{}
    requires upper != iset{}
    requires forall x <- lower, y <- upper :: x <= y
    ensures exists between: real :: IsUpperBound(lower, between) && IsLowerBound(upper, between)
  {
    assert exists between: real :: IsUpperBound(lower, between) && IsLowerBound(upper, between) by {
      var between := DedekindCompleteness(lower, upper);
      assert (forall x <- lower :: x <= between) && (forall x <- upper :: between <= x);
    }
  }

  ghost predicate IsInfimum(s: iset<real>, candidate: real) {
    && IsLowerBound(s, candidate)
    && forall other: real :: IsLowerBound(s, other) ==> other <= candidate
  }

  ghost function Infimum(s: iset<real>, lowerBound: real): (infimum: real)
    requires s != iset{}
    requires IsLowerBound(s, lowerBound)
    ensures IsInfimum(s, infimum)
  {
    var lowerBounds := iset x: real | IsLowerBound(s, x);
    assert lowerBound in lowerBounds;
    Completeness(lowerBounds, s);
    var infimum :| IsUpperBound(lowerBounds, infimum) && IsLowerBound(s, infimum);
    assert forall other: real :: IsLowerBound(s, other) ==> other <= infimum by {
      forall other: real ensures IsLowerBound(s, other) ==> other <= infimum {
        if IsLowerBound(s, other) {
          assert other in lowerBounds;
        }
      }
    }
    infimum
  }

  lemma InfimumIsUnique(s: iset<real>, infimum1: real, infimum2: real)
    requires IsInfimum(s, infimum1)
    requires IsInfimum(s, infimum2)
    ensures infimum1 == infimum2
  {}

  ghost predicate IsSupremum(s: iset<real>, candidate: real) {
    && IsUpperBound(s, candidate)
    && forall other: real :: IsUpperBound(s, other) ==> candidate <= other
  }

  ghost function Supremum(s: iset<real>, upperBound: real): (supremum: real)
    requires s != iset{}
    requires IsUpperBound(s, upperBound)
    ensures IsSupremum(s, supremum)
  {
    var upperBounds := iset x: real | IsUpperBound(s, x);
    assert upperBound in upperBounds;
    Completeness(s, upperBounds);
    var supremum :| IsUpperBound(s, supremum) && IsLowerBound(upperBounds, supremum);
    assert forall other: real :: IsUpperBound(s, other) ==> supremum <= other by {
      forall other: real ensures IsUpperBound(s, other) ==> supremum <= other {
        if IsUpperBound(s, other) {
          assert other in upperBounds;
        }
      }
    }
    supremum
  }

  lemma SupremumIsUnique(s: iset<real>, infimum1: real, infimum2: real)
    requires IsSupremum(s, infimum1)
    requires IsSupremum(s, infimum2)
    ensures infimum1 == infimum2
  {}
}

// As a sanity check for the above definitons, we prove the existence of the square root of 2:
module Sqrt2Proof {
  import RealArith
  import Reals

  function Square(x: real): real {
    x * x
  }

  lemma Sqrt2Exists() returns (sqrt2: real)
    ensures sqrt2 * sqrt2 == 2.0
  {
    var lower := iset x: real | x >= 0.0 && Square(x) < 2.0;
    var upper := iset x: real | x >= 0.0 && Square(x) > 2.0;
    forall x <- lower, y <- upper ensures x < y {
      if x >= y {
        calc {
          2.0;
        <
          Square(y);
        <= { RealArith.MulMonotonic(y, y, x); RealArith.MulMonotonic(x, y, x); }
          Square(x);
        <
          2.0;
        }
      }
    }
    assert 1.0 in lower;
    assert 2.0 in upper;
    sqrt2 := Reals.DedekindCompleteness(lower, upper);
    assert 1.0 <= sqrt2 <= 2.0;
    assert Square(sqrt2) == 2.0 by {
      if sqrt2 * sqrt2 > 2.0 {
        var eps := (sqrt2 * sqrt2 - 2.0) / (2.0 * sqrt2);
        assert 0.0 < eps < 1.0;
        var y := sqrt2 - eps;
        assert y * y > 2.0 by {
          calc {
            y * y;
            sqrt2 * sqrt2 - 2.0 * sqrt2 * eps + eps * eps;
            sqrt2 * sqrt2 - (sqrt2 * sqrt2 - 2.0) + eps * eps;
            2.0 + eps * eps;
          >
            2.0;
          }
        }
        assert y in upper by {
          assert y >= 0.0;
          assert y * y > 2.0;
        }
        assert false;
      }
      if sqrt2 * sqrt2 < 2.0 {
        var eps := (2.0 - sqrt2 * sqrt2) / (2.0 * sqrt2 + 1.0);
        assert 0.0 < eps < 1.0;
        var y := sqrt2 + eps;
        assert y * y < 2.0 by {
          calc {
            y * y;
            sqrt2 * sqrt2 + 2.0 * sqrt2 * eps + eps * eps;
            sqrt2 * sqrt2 + (2.0 * sqrt2 + eps) * eps;
          < { RealArith.MulMonotonicStrict(eps, 2.0 * sqrt2 + eps, 2.0 * sqrt2 + 1.0); }
            sqrt2 * sqrt2 + (2.0 * sqrt2 + 1.0) * eps;
            sqrt2 * sqrt2 + (2.0 - sqrt2 * sqrt2);
            2.0;
          }
        }
        assert y in lower by {
          assert y >= 0.0;
          assert y * y < 2.0;
        }
        assert false;
      }
    }
  }
}
