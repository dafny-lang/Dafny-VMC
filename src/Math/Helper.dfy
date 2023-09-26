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

  // See Logarithm.dfy in Stdlib
  function {:axiom} Log(base: nat, pow: nat): (log: nat)
    requires base > 1
    requires pow != 0
    ensures pow == 1 ==> log == 0
    ensures pow > 1 ==> log > 0
  // {
  //   if pow < base then 
  //     0
  //   else
  //     DivDecreases(pow, base);
  //     var log := 1 + Log(base, pow / base);
  //     assert log > 0;
  //     log
  // }

  /*******
   Lemmas  
  *******/

  lemma LemmaAboutNatDivision(a: nat, b: nat)
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

  lemma MultiplicationSubstitute(x: real, a: real, b: real)
    ensures a == b ==> (a * x == b * x)
  {}

  lemma DivisionByTwo(x: real)
    ensures 0.5 * x == x / 2.0
  {}

  lemma LemmaRealAssoc(x: real, y: real)
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

  lemma LemmaNatAssoc(a: nat, b: nat)
    requires b != 0
    ensures ((a as real) * (b as real)) / (b as real) == (a as real)
  {
    LemmaRealAssoc(a as real, b as real);
  }

  lemma LemmaNatDivision(a: nat, b: nat)
    requires b != 0
    ensures (a * b) / b == a
  {
    calc {
      (a * b) / b;
    == { LemmaAboutNatDivision(a * b, b); }
      ((a * b) as real / b as real).Floor;
    == { assert (a * b) as real == (a as real) * (b as real); }
      (((a as real) * (b as real)) / (b as real)).Floor;
    == { LemmaNatAssoc(a, b); }
      ((a as real)).Floor;
    ==
      a;
    }
  }

  lemma LemmaAboutPower(b: nat, n: int)
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
      == { LemmaNatDivision(Power(b, n - 1), b); }
        Power(b, n - 1);
      }
    }
  }

  // // See DivMod.dfy in StdLib
  // lemma DivDecreases(n: nat, d: nat)
  //   requires n != 0
  //   requires 1 < d
  //   ensures n / d < n
  // {
  //   calc {
  //     n / d;
  //   == { LemmaAboutNatDivision(n, d); }
  //     (n as real / d as real).Floor;
  //   < { assert n as real / d as real < n as real / 1 as real; }
  //     (n as real / 1 as real).Floor;
  //   ==
  //     (n as real).Floor;
  //   ==
  //     n;
  //   }
  // }

  // See Logarithm.dfy in Stdlib
  lemma {:axiom} LemmaLogPower(base: nat, n: nat)
    requires base > 1
    requires n != 0
    ensures Power(base, n) != 0
    ensures Log(base, Power(base, n)) == n
    ensures Power(base, Log(base, n)) == n

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
}