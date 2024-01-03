module Exponential {
  import NatArith
  import RealArith
  import Series

  ghost function Exp(x: real): real {
    ExpSeriesConverges(x);
    Series.Sum(ExpSeries(x))
  }

  // The sequence of summands of the exponential series
  function ExpSeries(gamma: real): nat -> real {
    (n: nat) => ExpTerm(gamma, n)
  }

  // ExpTerm(gamma, n) is gamma^n / n!, i.e. the n-th term in the power series of the exponential function.
  // The start parameter is useful for inductive proofs.
  opaque function ExpTerm(gamma: real, n: nat, start: nat := 1): real
    requires 1 <= start
  {
    NatArith.FactoralPositive(n, start);
    RealArith.Pow(gamma, n) / NatArith.Factorial(n, start) as real
  }

  // Decomposition of ExpTerm useful in inductive proofs.
  lemma ExpTermStep(gamma: real, n: nat, start: nat := 1)
    requires start >= 1
    requires n >= 1
    ensures ExpTerm(gamma, n, start) == ExpTerm(gamma, n - 1, start + 1) * (gamma / start as real)
  {
    NatArith.FactoralPositive(n, start);
    var denom := NatArith.Factorial(n, start) as real;
    var denom2 := (start * NatArith.Factorial(n - 1, start + 1)) as real;
    var numer := RealArith.Pow(gamma, n);
    var numer2 := gamma * RealArith.Pow(gamma, n - 1);
    calc {
      ExpTerm(gamma, n, start);
      { reveal ExpTerm(); }
      numer / denom;
      { reveal RealArith.Pow(); assert numer == numer2; }
      numer2 / denom;
      { reveal NatArith.Factorial(); assert denom == denom2; }
      numer2 / denom2;
      { reveal ExpTerm(); }
      ExpTerm(gamma, n - 1, start + 1) * (gamma / start as real);
    }
  }

  lemma {:axiom} ExpSeriesConverges(x: real)
    ensures Series.IsSummable(ExpSeries(x))

  lemma {:axiom} FunctionalEquation(x: real, y: real)
    ensures Exp(x + y) == Exp(x) * Exp(y)

  lemma {:axiom} Increasing(x: real, y: real)
    requires x < y
    ensures Exp(x) < Exp(y)

  lemma {:axiom} EvalOne()
    ensures 2.718281828 <= Exp(1.0) <= 2.718281829

  lemma Positive(x: real)
    ensures Exp(x) > 0.0
  {
    assert Exp(x) >= 0.0 by {
      var sqrt := Exp(x / 2.0);
      calc {
        Exp(x);
        { FunctionalEquation(x / 2.0, x / 2.0); }
        sqrt * sqrt;
      >=
        0.0;
      }
    }
    if Exp(x) == 0.0 {
      calc {
        0.0;
        Exp(x);
      < { Increasing(x, x + 1.0); }
        Exp(x + 1.0);
        { FunctionalEquation(x, 1.0); }
        Exp(x) * Exp(1.0);
      ==
        0.0;
      }
    }
  }

  lemma EvalZero()
    ensures Exp(0.0) == 1.0
  {
    var one := Exp(0.0);
    assert one > 0.0 by {
      Positive(0.0);
    }
    assert one * one == one by {
      FunctionalEquation(0.0, 0.0);
    }
  }
}
