/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Limits {
  import Reals
  import Sequences

  /************
   Definitions
  ************/

  ghost predicate SuffixIsClose(sequence: nat -> real, limit: real, epsilon: real, suffixStart: nat) {
    forall n: nat | n >= suffixStart :: Reals.Dist(sequence(n), limit) < epsilon
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

  /************
   Lemmas
  ************/

  lemma LimitIsUnique(sequence: nat -> real, limit1: real, limit2: real)
    requires ConvergesTo(sequence, limit1)
    requires ConvergesTo(sequence, limit2)
    ensures limit1 == limit2
  {
    if ConvergesTo(sequence, limit1) && ConvergesTo(sequence, limit2) && limit1 != limit2 {
      var epsilon := Reals.Dist(limit1, limit2) / 2.0;
      assert ExistsCloseSuffix(sequence, limit1, epsilon);
      var N1 : nat :| SuffixIsClose(sequence, limit1, epsilon, N1);
      assert ExistsCloseSuffix(sequence, limit2, epsilon);
      var N2 : nat :| SuffixIsClose(sequence, limit2, epsilon, N2);
      var N : nat :| N >= N1 && N >= N2;
      calc {
        Reals.Dist(limit1, limit2);
      <= { Reals.TriangleInequality(limit1, sequence(N), limit2); }
        Reals.Dist(limit1, sequence(N)) + Reals.Dist(sequence(N), limit2);
      <
        epsilon + epsilon;
      ==
        epsilon * 2.0;
      ==
        Reals.Dist(limit1, limit2);
      }
    }
  }

  lemma BoundOfConvergentSequence(sequence: nat -> real, limit: real) returns (bound: real)
    requires ConvergesTo(sequence, limit)
    ensures Sequences.IsBounded(sequence, bound)
    ensures bound > 0.0
  {
    assert ExistsCloseSuffix(sequence, limit, 1.0);
    var N: nat :| SuffixIsClose(sequence, limit, 1.0, N);
    bound := Reals.Abs(limit) + 1.0;
    for n := 0 to N
      invariant bound >= Reals.Abs(limit) + 1.0
      invariant forall i: nat | i < n :: Reals.Abs(sequence(i)) < bound
    {
      if Reals.Abs(sequence(n)) >= bound {
        bound := Reals.Abs(sequence(n)) + 1.0;
      }
    }
    assert forall n: nat | n < N :: Reals.Abs(sequence(n)) < bound;
    forall n: nat ensures Reals.Abs(sequence(n)) < bound {
      if n < N {
        assert Reals.Abs(sequence(n)) < bound;
      } else {
        assert Reals.Abs(sequence(n)) < Reals.Abs(limit) + 1.0 <= bound;
      }
    }
  }

  lemma ConstantSequenceConverges(constant: real)
    ensures ConvergesTo(Sequences.Constant(constant), constant)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(Sequences.Constant(constant), constant, epsilon) {
      assert SuffixIsClose(Sequences.Constant(constant), constant, epsilon, 0);
    }
  }

  lemma LimitIsAdditive(sequence1: nat -> real, limit1: real, sequence2: nat -> real, limit2: real)
    requires ConvergesTo(sequence1, limit1)
    requires ConvergesTo(sequence2, limit2)
    ensures ConvergesTo(Sequences.Add(sequence1, sequence2), limit1 + limit2)
  {
    var sumSequence := Sequences.Add(sequence1, sequence2);
    var sumLimit := limit1 + limit2;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(sumSequence, sumLimit, epsilon) {
      assert ExistsCloseSuffix(sequence1, limit1, epsilon / 2.0);
      var N1: nat :| SuffixIsClose(sequence1, limit1, epsilon / 2.0, N1);
      assert ExistsCloseSuffix(sequence2, limit2, epsilon / 2.0);
      var N2: nat :| SuffixIsClose(sequence2, limit2, epsilon / 2.0, N2);
      var N: nat :| N >= N1 && N >= N2;
      assert SuffixIsClose(sumSequence, sumLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Reals.Dist(sumSequence(n), sumLimit) < epsilon {
          calc {
            Reals.Dist(sumSequence(n), sumLimit);
          ==
            Reals.Dist(sequence1(n) + sequence2(n), limit1 + limit2);
          <=
            Reals.Dist(sequence1(n), limit1) + Reals.Dist(sequence2(n), limit2);
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
    ensures ConvergesTo(Sequences.Mul(sequence1, sequence2), limit1 * limit2)
  {
    var bound1 := BoundOfConvergentSequence(sequence1, limit1);
    var bound2 := BoundOfConvergentSequence(sequence2, limit2);
    var productSequence := Sequences.Mul(sequence1, sequence2);
    var productLimit := limit1 * limit2;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(productSequence, productLimit, epsilon) {
      var epsilon1 := epsilon / 2.0 / Reals.Max(Reals.Abs(limit2), 1.0);
      var epsilon2 := epsilon / 2.0 / Reals.Max(bound1, 1.0);
      assert ExistsCloseSuffix(sequence1, limit1, epsilon1);
      var N1: nat :| SuffixIsClose(sequence1, limit1, epsilon1, N1);
      assert ExistsCloseSuffix(sequence2, limit2, epsilon2);
      var N2: nat :| SuffixIsClose(sequence2, limit2, epsilon2, N2);
      var N: nat :| N >= N1 && N >= N2;
      assert SuffixIsClose(productSequence, productLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Reals.Dist(productSequence(n), productLimit) < epsilon {
          var s1 := sequence1(n);
          var s2 := sequence2(n);
          calc {
            Reals.Dist(productSequence(n), productLimit);
          == { assert productSequence(n) == s1 * s2; }
            Reals.Dist(s1 * s2, limit1 * limit2);
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
    requires Reals.Dist(s1, limit1) < epsilon / 2.0 / Reals.Max(Reals.Abs(limit2), 1.0)
    requires Reals.Dist(s2, limit2) < epsilon / 2.0 / Reals.Max(bound1, 1.0)
    requires Reals.Abs(s1) <= bound1
    ensures Reals.Dist(s1 * s2, limit1 * limit2) < epsilon
  {
    assert FirstSummand: Reals.Abs(limit2) * Reals.Dist(s1, limit1) <= epsilon / 2.0 by {
      var d1 := Reals.Max(Reals.Abs(limit2), 1.0);
      var epsilon1 := epsilon / 2.0 / Reals.Max(Reals.Abs(limit2), 1.0);
      calc {
        Reals.Abs(limit2) * Reals.Dist(s1, limit1);
      <= { Reals.MultiplicationMonotonic(Reals.Abs(limit2), Reals.Dist(s1, limit1), epsilon1); }
        Reals.Abs(limit2) * epsilon1;
      <=  { Reals.MultiplicationMonotonic(epsilon1, Reals.Abs(limit2), d1); }
        d1 * epsilon1;
      ==
        epsilon / 2.0;
      }
    }
    assert SecondSummand: bound1 * Reals.Dist(s2, limit2) < epsilon / 2.0 by {
      var d2 := Reals.Max(bound1, 1.0);
      var epsilon2 := epsilon / 2.0 / Reals.Max(bound1, 1.0);
      calc {
        bound1 * Reals.Dist(s2, limit2);
      < { Reals.MultiplicationMonotonicStrict(bound1, Reals.Dist(s2, limit2), epsilon2); }
        bound1 * epsilon2;
      <= { Reals.MultiplicationMonotonic(epsilon2, bound1, d2); }
        d2 * epsilon2;
      ==
        epsilon / 2.0;
      }
    }
    calc {
      Reals.Dist(s1 * s2, limit1 * limit2);
    <= { MultiplicationLimitHelper(s1, limit1, s2, limit2, bound1); }
      bound1 * Reals.Dist(s2, limit2) + Reals.Abs(limit2) * Reals.Dist(s1, limit1);
    < { reveal FirstSummand; reveal SecondSummand; }
      epsilon / 2.0 + epsilon / 2.0;
    ==
      epsilon;
    }
  }

  lemma MultiplicationLimitHelper(s1: real, limit1: real, s2: real, limit2: real, bound1: real)
    requires Reals.Abs(s1) <= bound1
    ensures Reals.Dist(s1 * s2, limit1 * limit2) <= bound1 * Reals.Dist(s2, limit2) + Reals.Abs(limit2) * Reals.Dist(s1, limit1)
  {
    calc {
      Reals.Dist(s1 * s2, limit1 * limit2);
    ==
      Reals.Abs(s1 * s2 - limit1 * limit2);
    ==
      Reals.Abs(s1 * (s2 - limit2) + limit2 * (s1 - limit1));
    <=
      Reals.Abs(s1 * (s2 - limit2)) + Reals.Abs(limit2 * (s1 - limit1));
    == { Reals.AbsMul(s1, s2 - limit2); }
      Reals.Abs(s1) * Reals.Abs(s2 - limit2) + Reals.Abs(limit2 * (s1 - limit1));
    == { Reals.AbsMul(limit2, s1 - limit1); }
      Reals.Abs(s1) * Reals.Abs(s2 - limit2) + Reals.Abs(limit2) * Reals.Abs(s1 - limit1);
    <=
      bound1 * Reals.Abs(s2 - limit2) + Reals.Abs(limit2) * Reals.Abs(s1 - limit1);
    ==
      bound1 * Reals.Dist(s2, limit2) + Reals.Abs(limit2) * Reals.Dist(s1, limit1);
    }
  }

  lemma LimitOfMultiplicationWithZeroSequence(sequence: nat -> real, bound: real, zero_seq: nat -> real)
    requires Sequences.IsBounded(sequence, bound)
    requires ConvergesTo(zero_seq, 0.0)
    ensures ConvergesTo(Sequences.Mul(sequence, zero_seq), 0.0)
  {
    var productSequence := Sequences.Mul(sequence, zero_seq);
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(productSequence, 0.0, epsilon) {
      var epsilon' := epsilon / Reals.Max(bound, 1.0);
      assert ExistsCloseSuffix(zero_seq, 0.0, epsilon');
      var N :| SuffixIsClose(zero_seq, 0.0, epsilon', N);
      assert SuffixIsClose(productSequence, 0.0, epsilon, N) by {
        forall n: nat | n >= N ensures Reals.Dist(productSequence(n), 0.0) < epsilon {
          var s := sequence(n);
          var z := zero_seq(n);
          calc {
            Reals.Dist(productSequence(n), 0.0);
          ==
            Reals.Abs(s * z);
          == { Reals.AbsMul(s, z); }
            Reals.Abs(s) * Reals.Abs(z);
          <= { Reals.MultiplicationMonotonic(Reals.Abs(s), Reals.Abs(z), epsilon'); }
            Reals.Abs(s) * epsilon';
          < { Reals.MultiplicationMonotonicStrict(epsilon', Reals.Abs(s), bound); }
            bound * epsilon';
          <= { Reals.MultiplicationMonotonic(epsilon', bound, Reals.Max(bound, 1.0)); }
            Reals.Max(bound, 1.0) * epsilon';
          ==
            epsilon;
          }
        }
      }
    }
  }

  lemma LimitOfInverse(sequence: nat -> real, limit: real)
    requires forall n: nat :: sequence(n) != 0.0
    requires limit != 0.0
    requires ConvergesTo(sequence, limit)
    ensures ConvergesTo(Sequences.Inverse(sequence), 1.0 / limit)
  {
    var invSeq := Sequences.Inverse(sequence);
    var invLimit := 1.0 / limit;
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(invSeq, invLimit, epsilon) {
      var limitSquared := limit * limit;
      var epsilon' := Reals.Min(Reals.Abs(limit) / 2.0, (epsilon * limitSquared) / 2.0);
      assert ExistsCloseSuffix(sequence, limit, epsilon');
      var N: nat :| SuffixIsClose(sequence, limit, epsilon', N);
      assert SuffixIsClose(invSeq, invLimit, epsilon, N) by {
        forall n: nat | n >= N ensures Reals.Dist(invSeq(n), invLimit) < epsilon {
          var s := sequence(n);
          calc {
            Reals.Dist(invSeq(n), invLimit);
          == { assert invSeq(n) == 1.0 / s; }
            Reals.Dist(1.0 / s, 1.0 / limit);
          == { LimitOfInverseHelper1(s, limit); }
            Reals.Dist(s, limit) / Reals.Abs(limit) / Reals.Abs(s);
          <= { LimitOfInverseHelper2(s, limit); }
            2.0 * Reals.Dist(s, limit) / limitSquared;
          < { Reals.DivisionIsMonotonicStrict(2.0 * Reals.Dist(s, limit), 2.0 * epsilon', limitSquared); }
            2.0 * epsilon' / limitSquared;
          <= { Reals.DivisionIsMonotonic(2.0 * epsilon', 2.0 * (epsilon * limitSquared) / 2.0, limitSquared); }
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
    ensures Reals.Dist(1.0 / s, 1.0 / limit) == Reals.Dist(s, limit) / Reals.Abs(limit) / Reals.Abs(s)
  {
    calc {
      Reals.Dist(1.0 / s, 1.0 / limit);
    ==
      Reals.Abs((limit - s) / (limit * s));
    == { Reals.DivMulEqualsDivDiv((limit - s), limit, s); }
      Reals.Abs((limit - s) / limit / s);
    == { Reals.AbsDiv((limit - s) / limit, s); }
      Reals.Abs((limit - s) / limit) / Reals.Abs(s);
    == { Reals.AbsDiv((limit - s), Reals.Abs(limit)); }
      Reals.Abs((limit - s)) / Reals.Abs(limit) / Reals.Abs(s);
    ==
      Reals.Dist(s, limit) / Reals.Abs(limit) / Reals.Abs(s);
    }
  }

  lemma LimitOfInverseHelper2(s: real, limit: real)
    requires s != 0.0
    requires limit != 0.0
    requires Reals.Abs(s) >= Reals.Abs(limit) / 2.0
    ensures limit * limit != 0.0
    ensures Reals.Dist(s, limit) / Reals.Abs(limit) / Reals.Abs(s) <= 2.0 * Reals.Dist(s, limit) / (limit * limit)
  {
    var AbsLimit := Reals.Abs(limit);
    assert AbsLimit > 0.0;
    assert AbsLimit * AbsLimit != 0.0 by {
      if AbsLimit * AbsLimit == 0.0 {
        var x := AbsLimit * AbsLimit;
        calc {
          x;
        ==
          0.0;
        <
          AbsLimit * AbsLimit;
        ==
          x;
        }
      }
    }
    assert Reals.Dist(s, limit) / Reals.Abs(limit) / Reals.Abs(s) <= 2.0 * Reals.Dist(s, limit) / (limit * limit) by {
      calc {
        Reals.Dist(s, limit) / AbsLimit / Reals.Abs(s);
      <= { Reals.DivisionIsAntiMonotonic(Reals.Dist(s, limit) / AbsLimit, Reals.Abs(s), AbsLimit / 2.0); }
        Reals.Dist(s, limit) / AbsLimit / (AbsLimit / 2.0);
      == { Reals.DivMulEqualsDivDiv2(Reals.Dist(s, limit) / AbsLimit, AbsLimit, 2.0); }
        Reals.Dist(s, limit) / AbsLimit * 2.0 / AbsLimit;
      == { Reals.DivMulEqualsMulDiv(Reals.Dist(s, limit), AbsLimit, 2.0); }
        Reals.Dist(s, limit) * 2.0 / AbsLimit / AbsLimit;
      == { Reals.DivMulEqualsDivDiv(2.0 * Reals.Dist(s, limit), AbsLimit, AbsLimit); }
        (2.0 * Reals.Dist(s, limit)) / (AbsLimit * AbsLimit);
      == { assert AbsLimit * AbsLimit == limit * limit; }
        2.0 * Reals.Dist(s, limit) / (limit * limit);
      }
    }
  }

  lemma OneOverNPlus1ConvergesToZero()
    ensures ConvergesTo(Sequences.OneOverNPlus1, 0.0)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(Sequences.OneOverNPlus1, 0.0, epsilon) {
      var epsilon_inv := 1.0 / epsilon;
      var N := epsilon_inv.Floor;
      assert SuffixIsClose(Sequences.OneOverNPlus1, 0.0, epsilon, N) by {
        forall n: nat ensures n >= N ==> Reals.Dist(Sequences.OneOverNPlus1(n), 0.0) < epsilon {
          assert Sequences.OneOverNPlus1(n) > 0.0;
          assert Reals.Dist(Sequences.OneOverNPlus1(n), 0.0) == Sequences.OneOverNPlus1(n);
          if n >= N {
            calc {
              Sequences.OneOverNPlus1(n);
            <= { Sequences.OneOverNPlus1IsAntimonotonic(N, n); }
              Sequences.OneOverNPlus1(N);
            ==
              1.0 / (N + 1) as real;
            < { Reals.DivisionIsAntiMonotonicStrict(1.0, (N + 1) as real, epsilon_inv); }
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
