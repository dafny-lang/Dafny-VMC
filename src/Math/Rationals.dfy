/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Rationals {
  /************
   Definitions
  ************/

  type PosInt = n: int | n >= 1 witness 1

  datatype Rational = Rational(numer: int, denom: PosInt) {
    predicate Eq(rhs: Rational) {
      this.numer * rhs.denom == rhs.numer * this.denom
    }

    predicate Leq(rhs: Rational) {
      this.numer * rhs.denom <= rhs.numer * this.denom
    }

    function Neg(): Rational {
      Rational(-this.numer, this.denom)
    }

    function Add(rhs: Rational): Rational {
      Rational(this.numer * rhs.denom + rhs.numer * this.denom, this.denom * rhs.denom)
    }

    function Sub(rhs: Rational): Rational {
      Add(rhs.Neg())
    }

    function Inv(): Rational
      requires this.numer != 0
    {
      var denom: int := this.denom;
      if this.numer < 0 then Rational(-denom, -this.numer) else Rational(denom, this.numer)
    }

    function Mul(rhs: Rational): Rational {
      Rational(this.numer * rhs.numer, this.denom * rhs.denom)
    }

    function Div(rhs: Rational): Rational
      requires rhs.numer != 0
    {
      Mul(rhs.Inv())
    }

    function Floor(): int {
      this.numer / this.denom
    }

    function FractionalPart(): Rational {
      Rational(this.numer % this.denom, this.denom)
    }

    function ToReal(): real {
      this.numer as real / this.denom as real
    }
  }

  function Int(n: int): Rational {
    Rational(n, 1)
  }

  /*******
   Lemmas
  *******/

  lemma RationalEqImpliesRealEq(lhs: Rational, rhs: Rational)
    requires lhs.Eq(rhs)
    ensures lhs.ToReal() == rhs.ToReal()
  {}

  lemma RealEqImpliesRationalEq(lhs: Rational, rhs: Rational)
    requires lhs.ToReal() == rhs.ToReal()
    ensures lhs.Eq(rhs)
  {}

  lemma RationalLeqImpliesRealLeq(lhs: Rational, rhs: Rational)
    requires lhs.Leq(rhs)
    ensures lhs.ToReal() <= rhs.ToReal()
  {}

  lemma RealLeqImpliesRationalLeq(lhs: Rational, rhs: Rational)
    requires lhs.ToReal() <= rhs.ToReal()
    ensures lhs.Leq(rhs)
  {}

  lemma NegIsCorrect(r: Rational)
    ensures r.Neg().ToReal() == -r.ToReal()
  {}

  lemma AddIsCorrect(lhs: Rational, rhs: Rational)
    ensures lhs.Add(rhs).ToReal() == lhs.ToReal() + rhs.ToReal()
  {}

  lemma SubIsCorrect(lhs: Rational, rhs: Rational)
    ensures lhs.Sub(rhs).ToReal() == lhs.ToReal() - rhs.ToReal()
  {}

  lemma InvIsCorrect(r: Rational)
    requires r.numer != 0
    ensures r.Inv().ToReal() == 1.0 / r.ToReal()
  {}

  lemma MulIsCorrect(lhs: Rational, rhs: Rational)
    ensures lhs.Mul(rhs).ToReal() == lhs.ToReal() * rhs.ToReal()
  {}

  lemma DivIsCorrect(lhs: Rational, rhs: Rational)
    requires rhs.numer != 0
    ensures lhs.Div(rhs).ToReal() == lhs.ToReal() / rhs.ToReal()
  {}

  lemma FractionAsFloor(a: int, b: nat)
    requires b != 0
    ensures a / b == (a as real / b as real).Floor
  {
    assert a as real / b as real == (a / b) as real + (a % b) as real / b as real by {
      assert a as real == (a / b) as real * b as real + (a % b) as real by {
        assert a == (a / b) * b + (a % b);
      }
    }
    if a < 0 {
    } else {
    }
  }

  lemma FloorIsCorrect(r: Rational)
    ensures r.Floor() == r.ToReal().Floor
  {
    var floor := r.numer / r.denom;
    var multiple := floor * r.denom;
    assert r.numer == multiple + r.numer % r.denom;
    var nextMultiple := multiple + r.denom;
    assert r.Floor() as real <= r.ToReal() by {
      calc {
        r.Floor() as real;
      ==
        (r.numer / r.denom) as real;
      == { assert r.numer / r.denom == (r.numer as real / r.denom as real).Floor by { FractionAsFloor(r.numer, r.denom); } }
        (r.numer as real / r.denom as real).Floor as real;
      <=
        r.numer as real / r.denom as real;
      ==
        r.ToReal();
      }
    }
    assert r.ToReal() < r.Floor() as real + 1.0 by {
      assert r.numer < nextMultiple;
      calc {
        r.ToReal();
      ==
        r.numer as real / r.denom as real;
      < { DivStrictlyMonotonic(r.denom as real, r.numer as real, nextMultiple as real); }
        nextMultiple as real / r.denom as real;
      ==
        (floor + 1) as real;
      ==
        r.Floor() as real + 1.0;
      }
    }
  }

  lemma FloorFractionalPartRelation(r: Rational)
    ensures r == Int(r.Floor()).Add(r.FractionalPart())
  {}

  lemma FractionalPartIsCorrect(r: Rational)
    ensures r.FractionalPart().ToReal() == r.ToReal() - r.ToReal().Floor as real
  {
    calc {
      r.FractionalPart().ToReal();
    == { FloorFractionalPartRelation(r); }
      r.Sub(Int(r.Floor())).ToReal();
    == { SubIsCorrect(r, Int(r.Floor())); }
      r.ToReal() - Int(r.Floor()).ToReal();
    ==
      r.ToReal() - r.Floor() as real;
    == { FloorIsCorrect(r); }
      r.ToReal() - r.ToReal().Floor as real;
    }
  }

  lemma DivStrictlyMonotonic(divisor: real, a: real, b: real)
    requires a < b
    requires divisor > 0.0
    ensures a / divisor < b / divisor
  {}
}
