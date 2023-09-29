/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Helper {
  /************
   Definitions
  ************/

  function Abs(x: real): real {
    if x < 0.0 then
      -x
    else
      x
  }

  function RealPower(b: real, n: nat): (p: real)
    ensures b > 0.0 ==> p > 0.0
  {
    match n
    case 0 => 1.0
    case 1 => b
    case _ => b * RealPower(b, n - 1)
  }

  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {
    match n
    case 0 => 1
    case 1 => b
    case _ => b * Power(b, n - 1)
  }

  // See LOG2_ML
  function Log2(n: nat): nat {
    if n == 0 then
      0
    else
      Log2(n / 2) + 1
  }


  /*******
   Lemmas
  *******/

  lemma NatDivisionHelper(a: nat, b: nat)
    requires b != 0
    ensures a / b == (a as real / b as real).Floor
  {
    assert a == (a / b) * b + (a % b);
    assert a as real == (a / b) as real * b as real + (a % b) as real;
    assert a as real / b as real == (a / b) as real + (a % b) as real / b as real;
  }

  lemma DivisionByOne(x: real)
    ensures x / (1 as real) == x
    ensures x / 1.0 == x
  {}

  lemma DivisionSubstitute(x: real, a: real, b: real)
    requires a == b
    requires a != 0.0 && b != 0.0
    ensures x / a == x / b
  {}

  lemma DivisionSubstituteAlternative(n: nat, a: nat, b: nat)
    requires a == b
    requires n != 0
    ensures a / n == b / n
  {}

  lemma DivisionSubstituteAlternativeReal(x: real, a: real, b: real)
    requires a == b
    requires x != 0.0
    ensures a / x == b / x
  {}

  lemma SmallDivMod(n: nat, m: nat)
    requires m > 0
    requires n < m
    ensures n / m == 0
    ensures n % m == n
  {}

  lemma DivModAddDenominator(n: nat, m: nat)
    requires m > 0
    ensures (n + m) / m == n / m + 1
    ensures (n + m) % m == n % m
  {
    var zp := (n + m) / m - n / m - 1;
    assert 0 == m * zp + ((n + m) % m) - (n % m);
  }

  lemma DivModIsUnique(n: nat, m: nat, a: nat, b: nat)
    requires m > 0
    requires b < m
    requires n == a * m + b
    ensures a == n / m
    ensures b == n % m
  {
    if a == 0 {
      assert n == b;
    } else {
      assert (n - m) / m == a - 1 && (n - m) % m == b by { DivModIsUnique(n - m, m, a - 1, b); }
      assert n / m == a && n % m == b by { DivModAddDenominator(n - m, m); }
    }
  }

  lemma DivModAddMultiple(a: nat, b: nat, c: nat)
    requires a > 0
    ensures (c * a + b) / a == c + b / a
    ensures (c * a + b) % a == b % a
  {
    calc {
      a * c + b;
    ==
      a * c + (a * (b / a) + b % a);
    ==
      a * (c + b / a) + b % a;
    }
    DivModIsUnique(a * c + b, a, c + b / a, b % a);
  }

  lemma MultiplicationSubstitute(x: real, a: real, b: real)
    requires a == b
    ensures a * x == b * x
  {}

  lemma InverseSubstitute(x: real, y: real)
    requires x != 0.0
    requires y != 0.0
    requires x == y
    ensures 1.0 / x == 1.0 / y
  {}

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {}

  lemma RealAssoc(x: real, y: real)
    requires y != 0.0
    ensures (x * y) / y == x
  {
    calc {
      (x * y) / y;
    ==
      x * (y / y);
    == { assert y / y == 1.0; }
      x * 1.0;
    ==
      x;
    }
  }

  lemma NatAssoc(a: nat, b: nat)
    requires b != 0
    ensures ((a as real) * (b as real)) / (b as real) == (a as real)
  {
    RealAssoc(a as real, b as real);
  }

  lemma NatDivision(a: nat, b: nat)
    requires b != 0
    ensures (a * b) / b == a
  {
    calc {
      (a * b) / b;
    == { NatDivisionHelper(a * b, b); }
      ((a * b) as real / b as real).Floor;
    == { assert (a * b) as real == (a as real) * (b as real); }
      (((a as real) * (b as real)) / (b as real)).Floor;
    == { NatAssoc(a, b); }
      ((a as real)).Floor;
    ==
      a;
    }
  }

  lemma PowerDivision(b: nat, n: int)
    requires b != 0 && n >= 1
    ensures Power(b, n) / b == Power(b, n - 1)
  {
    if n == 1 {
      calc {
        Power(b, n) / b;
      ==
        b / b;
      ==
        1;
      ==
        Power(b, 0);
      ==
        Power(b, n - 1);
      }
    } else {
      calc {
        Power(b, n) / b;
      == { }
        (b * Power(b, n - 1)) / b;
      == { }
        (Power(b, n - 1) * b) / b;
      == { NatDivision(Power(b, n - 1), b); }
        Power(b, n - 1);
      }
    }
  }

  // See DivMod.dfy in StdLib
  lemma DivDecreases(n: nat, d: nat)
    requires n >= 1
    requires 2 <= d
    ensures n / d < n
  {
    if n / d == 0 {} else {
      calc {
        n;
        ==
        (n / d) * d + (n % d);
        >=
        (n / d) * d;
        >=
        (n / d) * 2;
        >=
        (n / d) + (n / d);
        >
        n / d;
      }
    }
  }

  lemma MultiplicationIsMonotonic(factor: nat, x: int, y: int)
    requires x <= y
    ensures x * factor <= y * factor
  {}

  lemma SandwichBetweenPowers(base: nat, n: nat) returns (k: nat)
    requires base > 1
    requires n > 0
    decreases n
    ensures Power(base, k) <= n < Power(base, k + 1)
  {
    if n < base {
      k := 0;
      calc {
        Power(base, k);
        ==
        1;
        <=
        n;
        <
        base;
        ==
        Power(base, 1);
        ==
        Power(base, k + 1);
      }
    } else {
      assert n / base < n by {
        DivDecreases(n, base);
      }
      var k' := SandwichBetweenPowers(base, n / base);
      assert Power(base, k') <= n / base < Power(base, k' + 1);
      k := k' + 1;
      assert Power(base, k) <= n by {
        calc {
          Power(base, k);
          == { assert base >= 1; }
          Power(base, k') * base;
          <= { MultiplicationIsMonotonic(base, Power(base, k'), n / base); }
          (n / base) * base;
          <=
          (n / base) * base + (n % base);
          ==
          n;
        }
      }
      assert n < Power(base, k + 1) by {
        calc {
          n;
          ==
          (n / base) * base + (n % base);
          <
          (n / base) * base + base;
          ==
          (n / base + 1) * base;
          <= { MultiplicationIsMonotonic(base, n / base + 1, Power(base, k' + 1)); }
          Power(base, k' + 1) * base;
          ==
          Power(base, k + 1);
        }
      }
    }
  }

  lemma LemmaDivisionByTwo(n: nat)
    requires n != 0
    ensures n / 2 <= n - 1
  {
    if n == 1 {
      calc {
        n / 2;
      ==
        1 / 2;
      ==
        0;
      ==
        n - 1;
      }
    } else {
      calc {
        n / 2;
      ==
        (n as real / 2 as real).Floor;
      ==
        ((n - 1 + 1) as real / 2 as real).Floor;
      ==
        (((n - 1) as real / 2 as real) + (1 as real / 2 as real)).Floor;
      <=
        (((n - 1) as real / 2 as real) + 1.0).Floor;
      ==
        ((n - 1) as real / 2 as real).Floor + 1;
      <=
        n - 2 + 1;
      ==
        n - 1;
      }
    }
  }

  lemma AdditionOfFractions(x: real, y: real, z: real)
    requires z != 0.0
    ensures (x / z) + (y / z) == (x + y) / z
  {}

  lemma DivDivToDivMul(x: real, y: real, z: real)
    requires y != 0.0
    requires z != 0.0
    ensures (x / y) / z == x / (y * z)
  {}

  lemma NatMulNatToReal(x: nat, y: nat)
    ensures (x * y) as real == (x as real) * (y as real)
  {}

  lemma Log2LowerSuc(n: nat)
    ensures n + 1 <= Power(2, Log2(n))
  {}

  lemma Log2BothSides(n: nat)
    requires n != 0
    ensures Power(2, Log2(n) - 1) <= n < Power(2, Log2(n))
  {}

  lemma SimplifyFractions(x: real, y: real, z: real)
    requires z != 0.0
    requires y != 0.0
    ensures (x / z) / (y / z) == x / y
  {}

}
