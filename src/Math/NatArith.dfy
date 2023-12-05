module NatArith {
  function Max(a: nat, b: nat): nat {
    if a < b then b else a
  }

  function Min(a: nat, b: nat): nat {
    if a < b then a else b
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

  // TODO: a lot of functions from the helper module should go here.
}
