/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Limits {
  import RealArith
  import Reals
  import Sequences

  /************
   Definitions
  ************/

  ghost predicate SuffixIsClose(sequence: nat -> real, limit: real, epsilon: real, suffixStart: nat) {
    forall n: nat | n >= suffixStart :: RealArith.Dist(sequence(n), limit) < epsilon
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
      var epsilon := RealArith.Dist(limit1, limit2) / 2.0;
      assert ExistsCloseSuffix(sequence, limit1, epsilon);
      var N1 : nat :| SuffixIsClose(sequence, limit1, epsilon, N1);
      assert ExistsCloseSuffix(sequence, limit2, epsilon);
      var N2 : nat :| SuffixIsClose(sequence, limit2, epsilon, N2);
      var N : nat :| N >= N1 && N >= N2;
      calc {
        RealArith.Dist(limit1, limit2);
      <= { RealArith.TriangleInequality(limit1, sequence(N), limit2); }
        RealArith.Dist(limit1, sequence(N)) + RealArith.Dist(sequence(N), limit2);
      <
        epsilon + epsilon;
      ==
        epsilon * 2.0;
      ==
        RealArith.Dist(limit1, limit2);
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
    bound := RealArith.Abs(limit) + 1.0;
    for n := 0 to N
      invariant bound >= RealArith.Abs(limit) + 1.0
      invariant forall i: nat | i < n :: RealArith.Abs(sequence(i)) < bound
    {
      if RealArith.Abs(sequence(n)) >= bound {
        bound := RealArith.Abs(sequence(n)) + 1.0;
      }
    }
    assert forall n: nat | n < N :: RealArith.Abs(sequence(n)) < bound;
    forall n: nat ensures RealArith.Abs(sequence(n)) < bound {
      if n < N {
        assert RealArith.Abs(sequence(n)) < bound;
      } else {
        assert RealArith.Abs(sequence(n)) < RealArith.Abs(limit) + 1.0 <= bound;
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
        forall n: nat | n >= N ensures RealArith.Dist(sumSequence(n), sumLimit) < epsilon {
          calc {
            RealArith.Dist(sumSequence(n), sumLimit);
          ==
            RealArith.Dist(sequence1(n) + sequence2(n), limit1 + limit2);
          <=
            RealArith.Dist(sequence1(n), limit1) + RealArith.Dist(sequence2(n), limit2);
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
      var epsilon1 := epsilon / 2.0 / RealArith.Max(RealArith.Abs(limit2), 1.0);
      var epsilon2 := epsilon / 2.0 / RealArith.Max(bound1, 1.0);
      assert ExistsCloseSuffix(sequence1, limit1, epsilon1);
      var N1: nat :| SuffixIsClose(sequence1, limit1, epsilon1, N1);
      assert ExistsCloseSuffix(sequence2, limit2, epsilon2);
      var N2: nat :| SuffixIsClose(sequence2, limit2, epsilon2, N2);
      var N: nat :| N >= N1 && N >= N2;
      assert SuffixIsClose(productSequence, productLimit, epsilon, N) by {
        forall n: nat | n >= N ensures RealArith.Dist(productSequence(n), productLimit) < epsilon {
          var s1 := sequence1(n);
          var s2 := sequence2(n);
          calc {
            RealArith.Dist(productSequence(n), productLimit);
          == { assert productSequence(n) == sequence1(n) * sequence2(n) == s1 * s2; }
            RealArith.Dist(s1 * s2, limit1 * limit2);
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
    requires RealArith.Dist(s1, limit1) < epsilon / 2.0 / RealArith.Max(RealArith.Abs(limit2), 1.0)
    requires RealArith.Dist(s2, limit2) < epsilon / 2.0 / RealArith.Max(bound1, 1.0)
    requires RealArith.Abs(s1) <= bound1
    ensures RealArith.Dist(s1 * s2, limit1 * limit2) < epsilon
  {
    assert FirstSummand: RealArith.Abs(limit2) * RealArith.Dist(s1, limit1) <= epsilon / 2.0 by {
      var d1 := RealArith.Max(RealArith.Abs(limit2), 1.0);
      var epsilon1 := epsilon / 2.0 / RealArith.Max(RealArith.Abs(limit2), 1.0);
      calc {
        RealArith.Abs(limit2) * RealArith.Dist(s1, limit1);
      <= { RealArith.MulMonotonic(RealArith.Abs(limit2), RealArith.Dist(s1, limit1), epsilon1); }
        RealArith.Abs(limit2) * epsilon1;
      <=  { RealArith.MulMonotonic(epsilon1, RealArith.Abs(limit2), d1); }
        d1 * epsilon1;
      ==
        epsilon / 2.0;
      }
    }
    assert SecondSummand: bound1 * RealArith.Dist(s2, limit2) < epsilon / 2.0 by {
      var d2 := RealArith.Max(bound1, 1.0);
      var epsilon2 := epsilon / 2.0 / RealArith.Max(bound1, 1.0);
      calc {
        bound1 * RealArith.Dist(s2, limit2);
      < { RealArith.MulMonotonicStrict(bound1, RealArith.Dist(s2, limit2), epsilon2); }
        bound1 * epsilon2;
      <= { RealArith.MulMonotonic(epsilon2, bound1, d2); }
        d2 * epsilon2;
      ==
        epsilon / 2.0;
      }
    }
    calc {
      RealArith.Dist(s1 * s2, limit1 * limit2);
    <= { MultiplicationLimitHelper(s1, limit1, s2, limit2, bound1); }
      bound1 * RealArith.Dist(s2, limit2) + RealArith.Abs(limit2) * RealArith.Dist(s1, limit1);
    < { reveal FirstSummand; reveal SecondSummand; }
      epsilon / 2.0 + epsilon / 2.0;
    ==
      epsilon;
    }
  }

  lemma MultiplicationLimitHelper(s1: real, limit1: real, s2: real, limit2: real, bound1: real)
    requires RealArith.Abs(s1) <= bound1
    ensures RealArith.Dist(s1 * s2, limit1 * limit2) <= bound1 * RealArith.Dist(s2, limit2) + RealArith.Abs(limit2) * RealArith.Dist(s1, limit1)
  {
    calc {
      RealArith.Dist(s1 * s2, limit1 * limit2);
    ==
      RealArith.Abs(s1 * s2 - limit1 * limit2);
    ==
      RealArith.Abs(s1 * (s2 - limit2) + limit2 * (s1 - limit1));
    <=
      RealArith.Abs(s1 * (s2 - limit2)) + RealArith.Abs(limit2 * (s1 - limit1));
    == { RealArith.AbsMul(s1, s2 - limit2); }
      RealArith.Abs(s1) * RealArith.Abs(s2 - limit2) + RealArith.Abs(limit2 * (s1 - limit1));
    == { RealArith.AbsMul(limit2, s1 - limit1); }
      RealArith.Abs(s1) * RealArith.Abs(s2 - limit2) + RealArith.Abs(limit2) * RealArith.Abs(s1 - limit1);
    <=
      bound1 * RealArith.Abs(s2 - limit2) + RealArith.Abs(limit2) * RealArith.Abs(s1 - limit1);
    ==
      bound1 * RealArith.Dist(s2, limit2) + RealArith.Abs(limit2) * RealArith.Dist(s1, limit1);
    }
  }

  lemma LimitOfMultiplicationWithZeroSequence(sequence: nat -> real, bound: real, zeroSeq: nat -> real)
    requires Sequences.IsBounded(sequence, bound)
    requires ConvergesTo(zeroSeq, 0.0)
    ensures ConvergesTo(Sequences.Mul(sequence, zeroSeq), 0.0)
  {
    var productSequence := Sequences.Mul(sequence, zeroSeq);
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(productSequence, 0.0, epsilon) {
      var epsilon' := epsilon / RealArith.Max(bound, 1.0);
      assert ExistsCloseSuffix(zeroSeq, 0.0, epsilon');
      var N :| SuffixIsClose(zeroSeq, 0.0, epsilon', N);
      assert SuffixIsClose(productSequence, 0.0, epsilon, N) by {
        forall n: nat | n >= N ensures RealArith.Dist(productSequence(n), 0.0) < epsilon {
          var s := sequence(n);
          var z := zeroSeq(n);
          calc {
            RealArith.Dist(productSequence(n), 0.0);
          ==
            RealArith.Abs(s * z);
          == { RealArith.AbsMul(s, z); }
            RealArith.Abs(s) * RealArith.Abs(z);
          <= { RealArith.MulMonotonic(RealArith.Abs(s), RealArith.Abs(z), epsilon'); }
            RealArith.Abs(s) * epsilon';
          < { RealArith.MulMonotonicStrict(epsilon', RealArith.Abs(s), bound); }
            bound * epsilon';
          <= { RealArith.MulMonotonic(epsilon', bound, RealArith.Max(bound, 1.0)); }
            RealArith.Max(bound, 1.0) * epsilon';
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
      var epsilon' := RealArith.Min(RealArith.Abs(limit) / 2.0, (epsilon * limitSquared) / 2.0);
      assert ExistsCloseSuffix(sequence, limit, epsilon');
      var N: nat :| SuffixIsClose(sequence, limit, epsilon', N);
      assert SuffixIsClose(invSeq, invLimit, epsilon, N) by {
        forall n: nat | n >= N ensures RealArith.Dist(invSeq(n), invLimit) < epsilon {
          var s := sequence(n);
          calc {
            RealArith.Dist(invSeq(n), invLimit);
          == { assert invSeq(n) == 1.0 / s; }
            RealArith.Dist(1.0 / s, 1.0 / limit);
          == { LimitOfInverseHelper1(s, limit); }
            RealArith.Dist(s, limit) / RealArith.Abs(limit) / RealArith.Abs(s);
          <= { LimitOfInverseHelper2(s, limit); }
            2.0 * RealArith.Dist(s, limit) / limitSquared;
          < { RealArith.DivisionIsMonotonicStrict(2.0 * RealArith.Dist(s, limit), 2.0 * epsilon', limitSquared); }
            2.0 * epsilon' / limitSquared;
          <= { RealArith.DivisionIsMonotonic(2.0 * epsilon', 2.0 * (epsilon * limitSquared) / 2.0, limitSquared); }
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
    ensures RealArith.Dist(1.0 / s, 1.0 / limit) == RealArith.Dist(s, limit) / RealArith.Abs(limit) / RealArith.Abs(s)
  {
    calc {
      RealArith.Dist(1.0 / s, 1.0 / limit);
    ==
      RealArith.Abs((limit - s) / (limit * s));
    == { RealArith.DivMulEqualsDivDiv((limit - s), limit, s); }
      RealArith.Abs((limit - s) / limit / s);
    == { RealArith.AbsDiv((limit - s) / limit, s); }
      RealArith.Abs((limit - s) / limit) / RealArith.Abs(s);
    == { RealArith.AbsDiv((limit - s), RealArith.Abs(limit)); }
      RealArith.Abs((limit - s)) / RealArith.Abs(limit) / RealArith.Abs(s);
    ==
      RealArith.Dist(s, limit) / RealArith.Abs(limit) / RealArith.Abs(s);
    }
  }

  lemma LimitOfInverseHelper2(s: real, limit: real)
    requires s != 0.0
    requires limit != 0.0
    requires RealArith.Abs(s) >= RealArith.Abs(limit) / 2.0
    ensures limit * limit != 0.0
    ensures RealArith.Dist(s, limit) / RealArith.Abs(limit) / RealArith.Abs(s) <= 2.0 * RealArith.Dist(s, limit) / (limit * limit)
  {
    var AbsLimit := RealArith.Abs(limit);
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
    assert RealArith.Dist(s, limit) / RealArith.Abs(limit) / RealArith.Abs(s) <= 2.0 * RealArith.Dist(s, limit) / (limit * limit) by {
      calc {
        RealArith.Dist(s, limit) / AbsLimit / RealArith.Abs(s);
      <= { RealArith.DivisionIsAntiMonotonic(RealArith.Dist(s, limit) / AbsLimit, RealArith.Abs(s), AbsLimit / 2.0); }
        RealArith.Dist(s, limit) / AbsLimit / (AbsLimit / 2.0);
      == { RealArith.DivMulEqualsDivDiv2(RealArith.Dist(s, limit) / AbsLimit, AbsLimit, 2.0); }
        RealArith.Dist(s, limit) / AbsLimit * 2.0 / AbsLimit;
      == { RealArith.DivMulEqualsMulDiv(RealArith.Dist(s, limit), AbsLimit, 2.0); }
        RealArith.Dist(s, limit) * 2.0 / AbsLimit / AbsLimit;
      == { RealArith.DivMulEqualsDivDiv(2.0 * RealArith.Dist(s, limit), AbsLimit, AbsLimit); }
        (2.0 * RealArith.Dist(s, limit)) / (AbsLimit * AbsLimit);
      == { assert AbsLimit * AbsLimit == limit * limit; }
        2.0 * RealArith.Dist(s, limit) / (limit * limit);
      }
    }
  }

  lemma OneOverNPlus1ConvergesToZero()
    ensures ConvergesTo(Sequences.OneOverNPlus1, 0.0)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(Sequences.OneOverNPlus1, 0.0, epsilon) {
      var epsilonInv := 1.0 / epsilon;
      var N := epsilonInv.Floor;
      assert SuffixIsClose(Sequences.OneOverNPlus1, 0.0, epsilon, N) by {
        forall n: nat ensures n >= N ==> RealArith.Dist(Sequences.OneOverNPlus1(n), 0.0) < epsilon {
          assert Sequences.OneOverNPlus1(n) > 0.0;
          assert RealArith.Dist(Sequences.OneOverNPlus1(n), 0.0) == Sequences.OneOverNPlus1(n);
          if n >= N {
            calc {
              Sequences.OneOverNPlus1(n);
            <= { Sequences.OneOverNPlus1IsAntimonotonic(N, n); }
              Sequences.OneOverNPlus1(N);
            ==
              1.0 / (N + 1) as real;
            < { RealArith.DivisionIsAntiMonotonicStrict(1.0, (N + 1) as real, epsilonInv); }
              1.0 / epsilonInv;
            ==
              epsilon;
            }
          }
        }
      }
    }
  }
}
