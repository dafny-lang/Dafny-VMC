/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../Math/Helper.dfy"
include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"

module UniformPowerOfTwoModel {
  import Helper
  import RandomNumberGenerator
  import Quantifier
  import Monad
  import Independence
  import WhileAndUntil

  function UnifStepHelper(m: nat): bool -> Monad.Hurd<nat> {
    (b: bool) => Monad.Return(if b then 2*m + 1 else 2*m)
  }

  function UnifStep(m: nat): Monad.Hurd<nat> {
    Monad.Bind(Monad.Deconstruct, UnifStepHelper(m))
  }

  // Adapted from Definition 48 (see issue #79 for the reason of the modification)
  // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
  function Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n >= 1
  {
    if n == 1 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

  // A tail recursive version of Sample, closer to the imperative implementation
  function SampleTailRecursive(n: nat, u: nat := 0): Monad.Hurd<nat>
    requires n >= 1
  {
    (s: RandomNumberGenerator.RNG) =>
      if n == 1 then
        (u, s)
      else
        SampleTailRecursive(n / 2, if Monad.Head(s) then 2*u + 1 else 2*u)(Monad.Tail(s))
  }

  // Equivalence of Sample and its tail-recursive version
  lemma SampleCorrespondence(n: nat, s: RandomNumberGenerator.RNG)
    requires n >= 1
    ensures SampleTailRecursive(n)(s) == Sample(n)(s)
  {
    if n == 1 {
      assert SampleTailRecursive(n)(s) == Sample(n)(s);
    } else {
      var k := Log2Floor(n);
      assert Helper.Power(2, k) <= n < Helper.Power(2, k + 1) by { Power2OfLog2Floor(n); }
      calc {
        SampleTailRecursive(n)(s);
        { SampleTailRecursiveEqualIfSameLog2Floor(n, Helper.Power(2, k), k, 0, s); }
        SampleTailRecursive(Helper.Power(2, k))(s);
        Monad.Bind(Sample(Helper.Power(2, 0)), (u: nat) => SampleTailRecursive(Helper.Power(2, k), u))(s);
        { RelateWithTailRecursive(k, 0, s); }
        Sample(Helper.Power(2, k))(s);
        { SampleEqualIfSameLog2Floor(n, Helper.Power(2, k), k, s); }
        Sample(n)(s);
      }
    }
  }

  function Log2Floor(n: nat): nat
    requires n >= 1
    decreases n
  {
    if n < 2
    then 0
    else Log2Floor(n / 2) + 1
  }

  lemma PowerGreater0(base: nat, exponent: nat)
    requires base >= 2
    ensures Helper.Power(base, exponent) >= 1
  {}

  lemma Power2OfLog2Floor(n: nat)
    requires n >= 1
    ensures Helper.Power(2, Log2Floor(n)) <= n < Helper.Power(2, Log2Floor(n) + 1)
  {}

  // All numbers between consecutive powers of 2 behave the same as arguments to SampleTailRecursive
  lemma SampleTailRecursiveEqualIfSameLog2Floor(m: nat, n: nat, k: nat, u: nat, s: RandomNumberGenerator.RNG)
    requires m >= 1
    requires n >= 1
    requires Helper.Power(2, k) <= m < Helper.Power(2, k + 1)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures SampleTailRecursive(m, u)(s) == SampleTailRecursive(n, u)(s)
  {
    if k == 0 {
      assert m == n;
    } else {
      assert 1 <= m;
      assert 1 <= n;
      calc {
        SampleTailRecursive(m, u)(s);
        SampleTailRecursive(m / 2, if Monad.Head(s) then 2*u + 1 else 2*u)(Monad.Tail(s));
        { SampleTailRecursiveEqualIfSameLog2Floor(m / 2, n / 2, k - 1, if Monad.Head(s) then 2*u + 1 else 2*u, Monad.Tail(s)); }
        SampleTailRecursive(n / 2, if Monad.Head(s) then 2*u + 1 else 2*u)(Monad.Tail(s));
        SampleTailRecursive(n, u)(s);
      }
    }
  }

  // All numbers between consecutive powers of 2 behave the same as arguments to Sample
  lemma SampleEqualIfSameLog2Floor(m: nat, n: nat, k: nat, s: RandomNumberGenerator.RNG)
    requires m >= 1
    requires n >= 1
    requires Helper.Power(2, k) <= m < Helper.Power(2, k + 1)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures Sample(m)(s) == Sample(n)(s)
  {
    if k == 0 {
      assert m == n;
    } else {
      assert 1 <= m;
      assert 1 <= n;
      calc {
        Sample(m)(s);
        Monad.Bind(Sample(m / 2), UnifStep)(s);
        { SampleEqualIfSameLog2Floor(m / 2, n / 2, k - 1, s); }
        Monad.Bind(Sample(n / 2), UnifStep)(s);
        Sample(n)(s);
      }
    }
  }

  // The induction invariant for the equivalence proof (generalized version of SampleCorrespondence)
  lemma RelateWithTailRecursive(l: nat, m: nat, s: RandomNumberGenerator.RNG)
    decreases l
    ensures Monad.Bind(Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s) == Sample(Helper.Power(2, m + l))(s)
  {
    if l == 0 {
      calc {
        Monad.Bind(Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s);
        (var (u, s') := Sample(Helper.Power(2, m))(s); SampleTailRecursive(1, u)(s'));
        Sample(Helper.Power(2, m + l))(s);
      }
    } else {
      assert Ineq1: Helper.Power(2, l) >= 1 by { PowerGreater0(2, l); }
      assert Helper.Power(2, m) >= 1 by { PowerGreater0(2, m); }
      calc {
        Monad.Bind(Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s);
        (var (u, s') := Sample(Helper.Power(2, m))(s); SampleTailRecursive(Helper.Power(2, l), u)(s'));
        { reveal Ineq1; }
        (var (u, s') := Sample(Helper.Power(2, m))(s);
         SampleTailRecursive(Helper.Power(2, l) / 2, if Monad.Head(s') then 2 * u + 1 else 2 * u)(Monad.Tail(s')));
        { assert Helper.Power(2, m + 1) / 2 == Helper.Power(2, m); }
        (var (u', s') := Monad.Bind(Sample(Helper.Power(2, m)), UnifStep)(s);
         SampleTailRecursive(Helper.Power(2, l - 1), u')(s'));
        (var (u', s') := Sample(Helper.Power(2, m + 1))(s);
         SampleTailRecursive(Helper.Power(2, l - 1), u')(s'));
        Monad.Bind(Sample(Helper.Power(2, m + 1)), (u: nat) => SampleTailRecursive(Helper.Power(2, l - 1), u))(s);
        { RelateWithTailRecursive(l - 1, m + 1, s); }
        Sample(Helper.Power(2, m + l))(s);
      }
    }
  }
}
