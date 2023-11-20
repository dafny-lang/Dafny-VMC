/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Sequences {
  import RealArith
  import Reals

  ghost predicate Equal(sequence1: nat -> real, sequence2: nat -> real) {
    forall n: nat :: sequence1(n) == sequence2(n)
  }

  ghost predicate IsSuffixOf(suffix: nat -> real, full: nat -> real, prefix: nat) {
    forall n: nat :: suffix(n) == full(n + prefix)
  }

  ghost predicate IsBounded(sequence: nat -> real, bound: real) {
    forall n: nat :: RealArith.Abs(sequence(n)) < bound
  }

  function OneOverNPlus1(n: nat): real
  {
    1.0 / (n as real + 1.0)
  }

  function Suffix(sequence: nat -> real, len: nat): nat -> real {
    (n: nat) => sequence(n + len)
  }

  function Constant(constant: real): (nat -> real) {
    (_: nat) => constant
  }

  function Add(sequence1: nat -> real, sequence2: nat -> real): (nat -> real) {
    (n: nat) => sequence1(n) + sequence2(n)
  }

  function Mul(sequence1: nat -> real, sequence2: nat -> real): (nat -> real) {
    (n: nat) => sequence1(n) * sequence2(n)
  }

  function Inverse(sequence: nat -> real): nat -> real
    requires forall n: nat :: sequence(n) != 0.0
  {
    (n: nat) => 1.0 / sequence(n)
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
    == { RealArith.MultiplicationCancelMonotonic(mp1, 1.0 / np1, 1.0 / mp1); }
      1.0 / np1 <= 1.0 / mp1;
    ==
      OneOverNPlus1(m) >= OneOverNPlus1(n);
    }
  }
}
