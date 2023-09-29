/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Limits {
  /************
   Definitions
  ************/
  function Abs(r: real): real {
    if r >= 0.0 then r else -r
  }

  function Max(x: real, y: real): real {
    if x >= y then x else y
  }

  function Min(x: real, y: real): real {
    if x <= y then x else y
  }

  function Dist(x: real, y: real): real {
    Abs(x - y)
  }

  ghost predicate IsBounded(sequence: nat -> real, bound: real) {
    forall n: nat :: Abs(sequence(n)) < bound
  }

  ghost predicate SuffixIsClose(sequence: nat -> real, limit: real, epsilon: real, suffixStart: nat) {
    forall n: nat | n >= suffixStart :: Dist(sequence(n), limit) < epsilon
  }

  ghost predicate ExistsCloseSuffix(sequence: nat -> real, limit: real, epsilon: real) {
    exists N: nat :: SuffixIsClose(sequence, limit, epsilon, N)
  }

  ghost predicate ConvergesTo(sequence: nat -> real, limit: real)
  {
    forall epsilon: real | epsilon > 0.0 :: ExistsCloseSuffix(sequence, limit, epsilon)
  }

  ghost function Limit(sequence: nat -> real): real
    requires exists limit: real :: ConvergesTo(sequence, limit)
    ensures ConvergesTo(sequence, Limit(sequence))
  {
    var limit: real :| ConvergesTo(sequence, limit);
    limit
  }

  function OneOverNPlus1(n: nat): real
  {
    1.0 / (n as real + 1.0)
  }

  function constantSequence(constant: real): (nat -> real) {
    (_: nat) => constant
  }

  function addSequences(sequence1: nat -> real, sequence2: nat -> real): (nat -> real) {
    (n: nat) => sequence1(n) + sequence2(n)
  }

  function mulSequences(sequence1: nat -> real, sequence2: nat -> real): (nat -> real) {
    (n: nat) => sequence1(n) * sequence2(n)
  }

  function inverseSequence(sequence: nat -> real): nat -> real
    requires forall n: nat :: sequence(n) != 0.0
  {
    (n: nat) => 1.0 / sequence(n)
  }

  /************
   Lemmas
  ************/

  lemma TriangleInequality(a: real, b: real, c: real)
    ensures Dist(a, c) <= Dist(a, b) + Dist(b, c)
  {}

  lemma LimitIsUnique(sequence: nat -> real, limit1: real, limit2: real)
    requires ConvergesTo(sequence, limit1)
    requires ConvergesTo(sequence, limit2)
    ensures limit1 == limit2
  {
    if ConvergesTo(sequence, limit1) && ConvergesTo(sequence, limit2) && limit1 != limit2 {
      var epsilon := Dist(limit1, limit2) / 2.0;
      assert ExistsCloseSuffix(sequence, limit1, epsilon);
      var N1 : nat :| SuffixIsClose(sequence, limit1, epsilon, N1);
      assert ExistsCloseSuffix(sequence, limit2, epsilon);
      var N2 : nat :| SuffixIsClose(sequence, limit2, epsilon, N2);
      var N : nat :| N >= N1 && N >= N2;
      calc {
        Dist(limit1, limit2);
      <= { TriangleInequality(limit1, sequence(N), limit2); }
        Dist(limit1, sequence(N)) + Dist(sequence(N), limit2);
      <
        epsilon + epsilon;
      ==
        epsilon * 2.0;
      ==
        Dist(limit1, limit2);
      }
    }
  }

  lemma BoundOfConvergentSequence(sequence: nat -> real, limit: real) returns (bound: real)
    requires ConvergesTo(sequence, limit)
    ensures IsBounded(sequence, bound)
    ensures bound > 0.0
  {
    assert ExistsCloseSuffix(sequence, limit, 1.0);
    var N: nat :| SuffixIsClose(sequence, limit, 1.0, N);
    bound := Abs(limit) + 1.0;
    for n := 0 to N
      invariant bound >= Abs(limit) + 1.0
      invariant forall i: nat | i < n :: Abs(sequence(i)) < bound
    {
      if Abs(sequence(n)) >= bound {
        bound := Abs(sequence(n)) + 1.0;
      }
    }
    assert forall n: nat | n < N :: Abs(sequence(n)) < bound;
    forall n: nat ensures Abs(sequence(n)) < bound {
      if n < N {
        assert Abs(sequence(n)) < bound;
      } else {
        assert Abs(sequence(n)) < Abs(limit) + 1.0 <= bound;
      }
    }
  }

  lemma ConstantSequenceConverges(constant: real)
    ensures ConvergesTo(constantSequence(constant), constant)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(constantSequence(constant), constant, epsilon) {
      assert SuffixIsClose(constantSequence(constant), constant, epsilon, 0);
    }
  }

  lemma LimitIsAdditive(sequence1: nat -> real, limit1: real, sequence2: nat -> real, limit2: real)
    requires ConvergesTo(sequence1, limit1)
    requires ConvergesTo(sequence2, limit2)
    ensures ConvergesTo(addSequences(sequence1, sequence2), limit1 + limit2)
  {
    var sumSequence := addSequences(sequence1, sequence2);
    var sumLimit := limit1 + limit2;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(sumSequence, sumLimit, epsilon) {
      assert ExistsCloseSuffix(sequence1, limit1, epsilon / 2.0);
      var N1: nat :| SuffixIsClose(sequence1, limit1, epsilon / 2.0, N1);
      assert ExistsCloseSuffix(sequence2, limit2, epsilon / 2.0);
      var N2: nat :| SuffixIsClose(sequence2, limit2, epsilon / 2.0, N2);
      var N: nat :| N >= N1 && N >= N2;
      assert SuffixIsClose(sumSequence, sumLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Dist(sumSequence(n), sumLimit) < epsilon {
          calc {
            Dist(sumSequence(n), sumLimit);
          ==
            Dist(sequence1(n) + sequence2(n), limit1 + limit2);
          <=
            Dist(sequence1(n), limit1) + Dist(sequence2(n), limit2);
          <
            epsilon / 2.0 + epsilon / 2.0;
          ==
            epsilon;
          }
        }
      }
    }
  }

  lemma LimitIsMultiplicative(sequence1: nat -> real, limit1: real, sequence2: nat -> real, limit2: real)
    requires ConvergesTo(sequence1, limit1)
    requires ConvergesTo(sequence2, limit2)
    ensures ConvergesTo(mulSequences(sequence1, sequence2), limit1 * limit2)
  {
    var bound1 := BoundOfConvergentSequence(sequence1, limit1);
    var bound2 := BoundOfConvergentSequence(sequence2, limit2);
    var productSequence := mulSequences(sequence1, sequence2);
    var productLimit := limit1 * limit2;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(productSequence, productLimit, epsilon) {
      var epsilon1 := epsilon / 2.0 / Max(Abs(limit2), 1.0);
      var epsilon2 := epsilon / 2.0 / Max(bound1, 1.0);
      assert ExistsCloseSuffix(sequence1, limit1, epsilon1);
      var N1: nat :| SuffixIsClose(sequence1, limit1, epsilon1, N1);
      assert ExistsCloseSuffix(sequence2, limit2, epsilon2);
      var N2: nat :| SuffixIsClose(sequence2, limit2, epsilon2, N2);
      var N: nat :| N >= N1 && N >= N2;
      assert SuffixIsClose(productSequence, productLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Dist(productSequence(n), productLimit) < epsilon {
          var s1 := sequence1(n);
          var s2 := sequence2(n);
          calc {
            Dist(productSequence(n), productLimit);
          == { assert productSequence(n) == s1 * s2; }
            Dist(s1 * s2, limit1 * limit2);
          < { LimitIsMultiplicativeSuffixHelper(s1, limit1, s2, limit2, bound1, epsilon); }
            epsilon;
          }
        }
      }
    }
  }

  lemma LimitIsMultiplicativeSuffixHelper(s1: real, limit1: real, s2: real, limit2: real, bound1: real, epsilon: real)
    requires epsilon > 0.0
    requires bound1 > 0.0
    requires Dist(s1, limit1) < epsilon / 2.0 / Max(Abs(limit2), 1.0)
    requires Dist(s2, limit2) < epsilon / 2.0 / Max(bound1, 1.0)
    requires Abs(s1) <= bound1
    ensures Dist(s1 * s2, limit1 * limit2) < epsilon
  {
    assert FirstSummand: Abs(limit2) * Dist(s1, limit1) <= epsilon / 2.0 by {
      var d1 := Max(Abs(limit2), 1.0);
      var epsilon1 := epsilon / 2.0 / Max(Abs(limit2), 1.0);
      calc {
        Abs(limit2) * Dist(s1, limit1);
      <= { MultiplicationMonotonic(Abs(limit2), Dist(s1, limit1), epsilon1); }
        Abs(limit2) * epsilon1;
      <=  { MultiplicationMonotonic(epsilon1, Abs(limit2), d1); }
        d1 * epsilon1;
      ==
        epsilon / 2.0;
      }
    }
    assert SecondSummand: bound1 * Dist(s2, limit2) < epsilon / 2.0 by {
      var d2 := Max(bound1, 1.0);
      var epsilon2 := epsilon / 2.0 / Max(bound1, 1.0);
      calc {
        bound1 * Dist(s2, limit2);
      < { MultiplicationMonotonicStrict(bound1, Dist(s2, limit2), epsilon2); }
        bound1 * epsilon2;
      <= { MultiplicationMonotonic(epsilon2, bound1, d2); }
        d2 * epsilon2;
      ==
        epsilon / 2.0;
      }
    }
    calc {
      Dist(s1 * s2, limit1 * limit2);
    <= { MultiplicationLimitHelper(s1, limit1, s2, limit2, bound1); }
      bound1 * Dist(s2, limit2) + Abs(limit2) * Dist(s1, limit1);
    < { reveal FirstSummand; reveal SecondSummand; }
      epsilon / 2.0 + epsilon / 2.0;
    ==
      epsilon;
    }
  }

  lemma MultiplicationLimitHelper(s1: real, limit1: real, s2: real, limit2: real, bound1: real)
    requires Abs(s1) <= bound1
    ensures Dist(s1 * s2, limit1 * limit2) <= bound1 * Dist(s2, limit2) + Abs(limit2) * Dist(s1, limit1)
  {
    calc {
      Dist(s1 * s2, limit1 * limit2);
    ==
      Abs(s1 * s2 - limit1 * limit2);
    ==
      Abs(s1 * (s2 - limit2) + limit2 * (s1 - limit1));
    <=
      Abs(s1 * (s2 - limit2)) + Abs(limit2 * (s1 - limit1));
    == { AbsMul(s1, s2 - limit2); AbsMul(limit2, s1 - limit1); }
      Abs(s1) * Abs(s2 - limit2) + Abs(limit2) * Abs(s1 - limit1);
    <=
      bound1 * Abs(s2 - limit2) + Abs(limit2) * Abs(s1 - limit1);
    ==
      bound1 * Dist(s2, limit2) + Abs(limit2) * Dist(s1, limit1);
    }
  }

  lemma LimitOfMultiplicationWithZeroSequence(sequence: nat -> real, bound: real, zero_seq: nat -> real)
    requires IsBounded(sequence, bound)
    requires ConvergesTo(zero_seq, 0.0)
    ensures ConvergesTo(mulSequences(sequence, zero_seq), 0.0)
  {
    var productSequence := mulSequences(sequence, zero_seq);
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(productSequence, 0.0, epsilon) {
      var epsilon' := epsilon / Max(bound, 1.0);
      assert ExistsCloseSuffix(zero_seq, 0.0, epsilon');
      var N :| SuffixIsClose(zero_seq, 0.0, epsilon', N);
      assert SuffixIsClose(productSequence, 0.0, epsilon, N) by {
        forall n: nat | n >= N ensures Dist(productSequence(n), 0.0) < epsilon {
          var s := sequence(n);
          var z := zero_seq(n);
          calc {
            Dist(productSequence(n), 0.0);
          ==
            Abs(s * z);
          == { AbsMul(s, z); }
            Abs(s) * Abs(z);
          <= { MultiplicationMonotonic(Abs(s), Abs(z), epsilon'); }
            Abs(s) * epsilon';
          < { MultiplicationMonotonicStrict(epsilon', Abs(s), bound); }
            bound * epsilon';
          <= { MultiplicationMonotonic(epsilon', bound, Max(bound, 1.0)); }
            Max(bound, 1.0) * epsilon';
          ==
            epsilon;
          }
        }
      }
    }
  }

  lemma AbsMul(x: real, y: real)
    ensures Abs(x * y) == Abs(x) * Abs(y)
  {}

  lemma MultiplicationMonotonic(factor:real, x: real, y: real)
    requires factor >= 0.0
    ensures x <= y ==> x * factor <= y * factor
  {}

  lemma MultiplicationMonotonicStrict(factor:real, x: real, y: real)
    requires factor > 0.0
    ensures x < y ==> x * factor < y * factor
  {}

  lemma LimitOfInverse(sequence: nat -> real, limit: real)
    requires forall n: nat :: sequence(n) != 0.0
    requires limit != 0.0
    requires ConvergesTo(sequence, limit)
    ensures ConvergesTo(inverseSequence(sequence), 1.0 / limit)
  {
    var invSeq := inverseSequence(sequence);
    var invLimit := 1.0 / limit;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(invSeq, invLimit, epsilon) {
      var limitSquared := limit * limit;
      var epsilon' := Min(Abs(limit) / 2.0, (epsilon * limitSquared) / 2.0);
      assert ExistsCloseSuffix(sequence, limit, epsilon');
      var N: nat :| SuffixIsClose(sequence, limit, epsilon', N);
      assert SuffixIsClose(invSeq, invLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Dist(invSeq(n), invLimit) < epsilon {
          var s := sequence(n);
          calc {
            Dist(invSeq(n), invLimit);
          == { assert invSeq(n) == 1.0 / s; }
            Dist(1.0 / s, 1.0 / limit);
          == { LimitOfInverseHelper1(s, limit); }
            Dist(s, limit) / Abs(limit) / Abs(s);
          <= { LimitOfInverseHelper2(s, limit); }
            2.0 * Dist(s, limit) / limitSquared;
          < { DivisionIsMonotonicStrict(2.0 * Dist(s, limit), 2.0 * epsilon', limitSquared); }
            2.0 * epsilon' / limitSquared;
          <= { DivisionIsMonotonic(2.0 * epsilon', 2.0 * (epsilon * limitSquared) / 2.0, limitSquared); }
            2.0 * (epsilon * limitSquared) / 2.0 / limitSquared;
          == { assert 2.0 * (epsilon * limitSquared) / 2.0 == epsilon * limitSquared; }
            (epsilon * limitSquared) / limitSquared;
          ==
            epsilon;
          }
        }
      }
    }
  }

  lemma LimitOfInverseHelper1(s: real, limit: real)
    requires s != 0.0
    requires limit != 0.0
    ensures Dist(1.0 / s, 1.0 / limit) == Dist(s, limit) / Abs(limit) / Abs(s)
  {
    calc {
      Dist(1.0 / s, 1.0 / limit);
    ==
      Abs((limit - s) / (limit * s));
    == { DivMulEqualsDivDiv((limit - s), limit, s); }
      Abs((limit - s) / limit / s);
    == { AbsDiv((limit - s) / limit, s); }
      Abs((limit - s) / limit) / Abs(s);
    == { AbsDiv((limit - s), Abs(limit)); }
      Abs((limit - s)) / Abs(limit) / Abs(s);
    ==
      Dist(s, limit) / Abs(limit) / Abs(s);
    }
  }

  lemma LimitOfInverseHelper2(s: real, limit: real)
    requires s != 0.0
    requires limit != 0.0
    requires Abs(s) >= Abs(limit) / 2.0
    ensures limit * limit != 0.0
    ensures Dist(s, limit) / Abs(limit) / Abs(s) <= 2.0 * Dist(s, limit) / (limit * limit)
  {
    var absLimit := Abs(limit);
    assert absLimit > 0.0;
    assert absLimit * absLimit != 0.0 by {
      if absLimit * absLimit == 0.0 {
        var x := absLimit * absLimit;
        calc {
          x;
        ==
          0.0;
        <
          absLimit * absLimit;
        ==
          x;
        }
      }
    }
    assert Dist(s, limit) / Abs(limit) / Abs(s) <= 2.0 * Dist(s, limit) / (limit * limit) by {
      calc {
        Dist(s, limit) / absLimit / Abs(s);
      <= { DivisionIsAntiMonotonic(Dist(s, limit) / absLimit, Abs(s), absLimit / 2.0); }
        Dist(s, limit) / absLimit / (absLimit / 2.0);
      == { DivMulEqualsDivDiv2(Dist(s, limit) / absLimit, absLimit, 2.0); }
        Dist(s, limit) / absLimit * 2.0 / absLimit;
      == { DivMulEqualsMulDiv(Dist(s, limit), absLimit, 2.0); }
        Dist(s, limit) * 2.0 / absLimit / absLimit;
      == { DivMulEqualsDivDiv(2.0 * Dist(s, limit), absLimit, absLimit); }
        (2.0 * Dist(s, limit)) / (absLimit * absLimit);
      == { assert absLimit * absLimit == limit * limit; }
        2.0 * Dist(s, limit) / (limit * limit);
      }
    }
  }

  lemma DivMulEqualsMulDiv(a: real, b: real, c: real)
    requires b != 0.0
    ensures a / b * c == a * c / b
  {}

  lemma DivMulEqualsDivDiv(a: real, b: real, c: real)
    requires b != 0.0
    requires c != 0.0
    ensures a / (b * c) == a / b / c
  {}

  lemma DivMulEqualsDivDiv2(a: real, b: real, c: real)
    requires b != 0.0
    requires c != 0.0
    ensures a / (b / c) == a * c / b
  {}

  lemma AbsDiv(a: real, b: real)
    requires b != 0.0
    ensures Abs(a / b) == Abs(a) / Abs(b)
  {
    assume false;
  }

  lemma OneOverNPlus1IsAntimonotonic(m: nat, n: nat)
    requires m <= n
    ensures OneOverNPlus1(m) >= OneOverNPlus1(n)
  {
    var mp1 := (m + 1) as real;
    var np1 := (n + 1) as real;
    assert mp1 > 0.0;
    assert np1 > 0.0;
    calc {
      mp1 <= np1;
    ==
      mp1 / np1 <= 1.0;
    ==
      (1.0 / np1) * mp1 <= (1.0 / mp1) * mp1;
    == { MultiplicationCancelMonotonic(mp1, 1.0 / np1, 1.0 / mp1); }
      1.0 / np1 <= 1.0 / mp1;
    ==
      OneOverNPlus1(m) >= OneOverNPlus1(n);
    }
  }

  lemma MultiplicationCancelMonotonic(factor:real, x: real, y: real)
    requires factor > 0.0
    ensures x * factor <= y * factor ==> x <= y
  {}

  lemma DivisionIsMonotonic(a: real, b: real, c: real)
    requires c > 0.0
    requires a <= b
    ensures a / c <= b / c
  {}

  lemma DivisionIsMonotonicStrict(a: real, b: real, c: real)
    requires c > 0.0
    requires a < b
    ensures a / c < b / c
  {}

  lemma DivisionIsAntiMonotonic(a: real, b: real, c: real)
    requires a >= 0.0
    requires b > 0.0
    requires c > 0.0
    requires c <= b
    ensures a / b <= a / c
  {}

  lemma DivisionIsAntiMonotonicStrict(a: real, b: real, c: real)
    requires a > 0.0
    requires b > 0.0
    requires c > 0.0
    ensures (c < b) <==> (a / b < a / c)
  {}

  lemma OneOverNPlus1ConvergesToZero()
    ensures ConvergesTo(OneOverNPlus1, 0.0)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(OneOverNPlus1, 0.0, epsilon) {
      var epsilon_inv := 1.0 / epsilon;
      var N := epsilon_inv.Floor;
      assert SuffixIsClose(OneOverNPlus1, 0.0, epsilon, N) by {
        forall n: nat ensures n >= N ==> Dist(OneOverNPlus1(n), 0.0) < epsilon {
          assert OneOverNPlus1(n) > 0.0;
          assert Dist(OneOverNPlus1(n), 0.0) == OneOverNPlus1(n);
          if n >= N {
            calc {
              OneOverNPlus1(n);
            <= { OneOverNPlus1IsAntimonotonic(N, n); }
              OneOverNPlus1(N);
            ==
              1.0 / (N + 1) as real;
            < { DivisionIsAntiMonotonicStrict(1.0, (N + 1) as real, epsilon_inv); }
              1.0 / epsilon_inv;
            ==
              epsilon;
            }
          }
        }
      }
    }
  }
}
