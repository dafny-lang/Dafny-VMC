module NatArith {
  function Max(a: nat, b: nat): nat {
    if a < b then b else a
  }

  function Min(a: nat, b: nat): nat {
    if a < b then a else b
  }

  function Factorial(n: nat, start: nat := 1): nat {
    if n == 0 then 1 else start * Factorial(n - 1, start + 1)
  }

  lemma FactoralPositive(n: nat, start: nat := 1)
    requires start >= 1
    ensures Factorial(n, start) >= 1
  {}

  // TODO: a lot of functions from the helper module should go here.
}
