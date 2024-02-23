/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Limits {
  import RealArith
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

  ghost predicate Converges(sequence: nat -> real) {
    exists limit: real :: ConvergesTo(sequence, limit)
  }

  ghost function Limit(sequence: nat -> real): real
    requires Converges(sequence)
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

  // This would be trivial if Dafny had function extensionality
  lemma LimitOfEqualsIsEqual(sequence1: nat -> real, sequence2: nat -> real, limit: real)
    requires forall n: nat :: sequence1(n) == sequence2(n)
    requires ConvergesTo(sequence1, limit)
    ensures ConvergesTo(sequence2, limit)
  {
    assert Sequences.IsSuffixOf(sequence2, sequence1, 0);
    SuffixConvergesToSame(sequence1, sequence2, 0, limit);
  }

  lemma SuffixConvergesToSame(sequence: nat -> real, suffix: nat -> real, prefix: nat, limit: real)
    requires Sequences.IsSuffixOf(suffix, sequence, prefix)
    ensures ConvergesTo(suffix, limit) <==> ConvergesTo(sequence, limit)
  {
    forall epsilon: real | epsilon > 0.0 ensures ExistsCloseSuffix(suffix, limit, epsilon) <==> ExistsCloseSuffix(sequence, limit, epsilon) {
      if N: nat :| SuffixIsClose(sequence, limit, epsilon, N) {
        assert SuffixIsClose(sequence, limit, epsilon, N + prefix);
        assert SuffixIsClose(suffix, limit, epsilon, N);
      }
      if N: nat :| SuffixIsClose(suffix, limit, epsilon, N) {
        assert SuffixIsClose(sequence, limit, epsilon, N + prefix) by {
          forall n: nat | n >= N + prefix ensures RealArith.Dist(sequence(n), limit) < epsilon {
            var n' := n - prefix;
            assert sequence(n) == suffix(n');
          }
        }
      }
    }
  }

}
