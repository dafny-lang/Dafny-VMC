module NatArith {
  function Max(a: nat, b: nat): nat {
    if a < b then b else a
  }

  function Min(a: nat, b: nat): nat {
    if a < b then a else b
  }

  function Power(b: nat, n: nat): (p: nat)
    ensures b > 0 ==> p > 0
  {
    match n
    case 0 => 1
    case 1 => b
    case _ => b * Power(b, n - 1)
  }

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {
    if n < 2
    then 0
    else Log2Floor(n / 2) + 1
  }

  lemma Log2FloorDef(n: nat)
    requires n >= 1
    ensures Log2Floor(2 * n) == Log2Floor(n) + 1
  {}

  function boolToNat(b: bool): nat {
    if b then 1 else 0
  }

  // Computes the rising factorial start^(n),
  // i.e. the product `start * (start + 1) * ... * (start + n - 1)`, i.e. with n factors.
  // see: https://en.wikipedia.org/wiki/Falling_and_rising_factorials
  // With the default value of start = 1, it computes n!
  // The start parameter is useful for inductive proofs.
  opaque function Factorial(n: nat, start: nat := 1): nat {
    if n == 0 then 1 else start * Factorial(n - 1, start + 1)
  }

  lemma FactoralPositive(n: nat, start: nat := 1)
    requires start >= 1
    ensures Factorial(n, start) >= 1
  {
    reveal Factorial();
  }

  opaque function FactorialTraditional(n: nat): (fact: nat) 
    ensures fact != 0
  {
    if n == 0 then 1 else n * FactorialTraditional(n - 1)
  }

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 1
    ensures Power(base, exponent) >= 1
  {}

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Power(2, Log2Floor(n)) <= n < Power(2, Log2Floor(n) + 1)
  {}

  lemma NLtPower2Log2FloorOf2N(n: nat)
    requires n >= 1
    ensures n < Power(2, Log2Floor(2 * n))
  {
    calc {
      n;
    < { Power2OfLog2Floor(n); }
      Power(2, Log2Floor(n) + 1);
    == { Log2FloorDef(n); }
      Power(2, Log2Floor(2 * n));
    }
  }

  lemma MulMonotonic(a: nat, b: nat, c: nat, d: nat)
    requires a <= c
    requires b <= d
    ensures a * b <= c * d
  {
    calc {
      a * b;
    <=
      c * b;
    <=
      c * d;
    }
  }
}
