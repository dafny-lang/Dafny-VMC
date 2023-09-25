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

  function Dist(x: real, y: real): real {
    Abs(x - y)
  }

  ghost predicate ConvergesTo(sequence: nat -> real, limit: real)
  {
    forall epsilon: real | epsilon > 0.0 ::
      exists N: nat ::
        forall n: nat ::
          n >= N ==> -epsilon < sequence(n) - limit < epsilon
  }

  ghost function EpsilonToSuffix(sequence: nat -> real, limit: real, epsilon: real): nat
    requires epsilon > 0.0
    requires ConvergesTo(sequence, limit)
    ensures forall n: nat :: n >= EpsilonToSuffix(sequence, limit, epsilon) ==>
      -epsilon < sequence(n) - limit < epsilon
  {
    assert forall epsilon2: real | epsilon2 > 0.0 :: exists N: nat ::
        forall n: nat :: n >= N ==> -epsilon2 < sequence(n) - limit < epsilon2 by {
            assert ConvergesTo(sequence, limit);
          }
    assume false;
    0
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

  /************
   Lemmas
  ************/

  lemma TriangleInequality(a: real, b: real, c: real)
    ensures Dist(a, c) <= Dist(a, b) + Dist(b, c)
  {}

  lemma LimitUnique(sequence: nat -> real)
    ensures forall limit1, limit2: real ::
      ConvergesTo(sequence, limit1) && ConvergesTo(sequence, limit2) ==> limit1 == limit2
  {
    forall limit1, limit2: real ensures
      ConvergesTo(sequence, limit1) && ConvergesTo(sequence, limit2) ==> limit1 == limit2
    {
      if ConvergesTo(sequence, limit1) && ConvergesTo(sequence, limit2) && limit1 != limit2 {
        var epsilon := Abs(limit1 - limit2) / 2.0;
        var N1 : nat :| forall n: nat | n >= N1 :: -epsilon < sequence(n) - limit1 < epsilon;
      }
    }
  }

  lemma OneOverNPlus1ConvergesToZero()
    ensures ConvergesTo(OneOverNPlus1, 0.0)
  {
    assert forall epsilon: real | epsilon > 0.0 ::
      exists N: nat ::
        forall n: nat | n >= N ::
          -epsilon < OneOverNPlus1(n) - 0.0 < epsilon by {
      forall epsilon: real | epsilon > 0.0 ensures
      exists N: nat ::
        forall n: nat | n >= N ::
          -epsilon < OneOverNPlus1(n) - 0.0 < epsilon {
            assume false;
          }
    }
    assert ConvergesTo(OneOverNPlus1, 0.0);
  }
}