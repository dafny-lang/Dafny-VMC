/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Rationals {
  /************
   Definitions
  ************/

  type PosInt = n: int | n >=1 witness 1

  datatype Rational = Rational(numer: int, denom: PosInt)

  predicate Eq(lhs: Rational, rhs: Rational) {
    lhs.numer * rhs.denom == rhs.numer * lhs.denom
  }

  predicate Leq(lhs: Rational, rhs: Rational) {
    lhs.numer * rhs.denom <= rhs.numer * lhs.denom
  }

  function Int(n: int): Rational {
    Rational(n, 1)
  }

  function Neg(arg: Rational): Rational {
    Rational(-arg.numer, arg.denom)
  }

  function Add(lhs: Rational, rhs: Rational): Rational {
    Rational(lhs.numer * rhs.denom + rhs.numer * lhs.denom, lhs.denom * rhs.denom)
  }

  function Sub(lhs: Rational, rhs: Rational): Rational {
    Add(lhs, Neg(rhs))
  }

  function Inv(arg: Rational): Rational
    requires arg.numer != 0
  {
    var denom: int := arg.denom;
    if arg.numer < 0 then Rational(-denom, -arg.numer) else Rational(denom, arg.numer)
  }

  function Mul(lhs: Rational, rhs: Rational): Rational {
    Rational(lhs.numer * rhs.numer, lhs.denom * rhs.denom)
  }

  function Div(lhs: Rational, rhs: Rational): Rational
    requires rhs.numer != 0
  {
    Mul(lhs, Inv(rhs))
  }

  function Floor(r: Rational): int {
    r.numer / r.denom
  }

  function FractionalPart(r: Rational): Rational {
    Rational(r.numer % r.denom, r.denom)
  }

  function ToReal(r: Rational): real {
    r.numer as real / r.denom as real
  }

  /*******
   Lemmas
  *******/

  lemma RationalEqImpliesRealEq(lhs: Rational, rhs: Rational)
    requires Eq(lhs, rhs)
    ensures ToReal(lhs) == ToReal(rhs)
  {}

  lemma RealEqImpliesRationalEq(lhs: Rational, rhs: Rational)
    requires ToReal(lhs) == ToReal(rhs)
    ensures Eq(lhs, rhs)
  {}

  lemma RationalLeqImpliesRealLeq(lhs: Rational, rhs: Rational)
    requires Leq(lhs, rhs)
    ensures ToReal(lhs) <= ToReal(rhs)
  {}

  lemma RealLeqImpliesRationalLeq(lhs: Rational, rhs: Rational)
    requires ToReal(lhs) <= ToReal(rhs)
    ensures Leq(lhs, rhs)
  {}

  lemma NegIsCorrect(r: Rational)
    ensures ToReal(Neg(r)) == -ToReal(r)
  {}

  lemma AddIsCorrect(lhs: Rational, rhs: Rational)
    ensures ToReal(Add(lhs, rhs)) == ToReal(lhs) + ToReal(rhs)
  {}

  lemma SubIsCorrect(lhs: Rational, rhs: Rational)
    ensures ToReal(Sub(lhs, rhs)) == ToReal(lhs) - ToReal(rhs)
  {}

  lemma InvIsCorrect(r: Rational)
    requires r.numer != 0
    ensures ToReal(Inv(r)) == 1.0 / ToReal(r)
  {}

  lemma MulIsCorrect(lhs: Rational, rhs: Rational)
    ensures ToReal(Mul(lhs, rhs)) == ToReal(lhs) * ToReal(rhs)
  {}

  lemma DivIsCorrect(lhs: Rational, rhs: Rational)
    requires rhs.numer != 0
    ensures ToReal(Div(lhs, rhs)) == ToReal(lhs) / ToReal(rhs)
  {}

  lemma FloorIsCorrect(r: Rational)
    ensures Floor(r) == ToReal(r).Floor
  {
    var floor := r.numer / r.denom;
    var multiple := floor * r.denom;
    assert r.numer == multiple + r.numer % r.denom;
    var next_multiple := multiple + r.denom;
    assert Floor(r) as real <= ToReal(r);
    assert ToReal(r) < Floor(r) as real + 1.0 by {
      assert r.numer < next_multiple;
      calc {
        ToReal(r);
        ==
        r.numer as real / r.denom as real;
        < { DivStrictlyMonotonic(r.denom as real, r.numer as real, next_multiple as real); }
        next_multiple as real / r.denom as real;
        ==
        (floor + 1) as real;
        ==
        Floor(r) as real + 1.0;
      }
    }
  }

  lemma FloorFractionalPartRelation(r: Rational)
    ensures r == Add(Int(Floor(r)), FractionalPart(r))
  {}

  lemma FractionalPartIsCorrect(r: Rational)
    ensures ToReal(FractionalPart(r)) == ToReal(r) - ToReal(r).Floor as real
  {
    calc {
      ToReal(FractionalPart(r));
      == { FloorFractionalPartRelation(r); }
      ToReal(Sub(r, Int(Floor(r))));
      == { SubIsCorrect(r, Int(Floor(r))); }
      ToReal(r) - ToReal(Int(Floor(r)));
      ==
      ToReal(r) - Floor(r) as real;
      == { FloorIsCorrect(r); }
      ToReal(r) - ToReal(r).Floor as real;
    }
  }

  lemma DivStrictlyMonotonic(divisor: real, a: real, b: real)
    requires a < b
    requires divisor > 0.0
    ensures a / divisor < b / divisor
  {}
}
