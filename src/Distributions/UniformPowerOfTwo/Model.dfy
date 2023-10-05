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

module Model {
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

  // Definition 48
  function Sample(n: nat): (h: Monad.Hurd<nat>) {
    if n == 0 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

  // A tail recursive version of Sample, closer to the imperative implementation
  function SampleTailRecursive(n: nat, u: nat := 0): Monad.Hurd<nat>
    decreases n
  {
    (s: RandomNumberGenerator.RNG) =>
      if n == 0 then
        (u, s)
      else
        SampleTailRecursive(n / 2, if Monad.Head(s) then 2*u + 1 else 2*u)(Monad.Tail(s))
  }

  // Equivalence of Sample and its tail-recursive version
  lemma SampleCorrespondence(n: nat, s: RandomNumberGenerator.RNG)
    ensures SampleTailRecursive(n)(s) == Sample(n)(s)
  {
    if n == 0 {
      assert SampleTailRecursive(n)(s) == Sample(n)(s);
    } else {
      var k := Helper.Log2(n);
      assert Power2(k - 1) <= n < Power2(k) by { Power2OfLog2(n); }
      calc {
        SampleTailRecursive(n)(s);
        { SampleTailRecursiveEqualIfSameLog2Floor(n, Power2(k - 1), k, 0, s); }
        SampleTailRecursive(Power2(k - 1))(s);
        Monad.Bind(Sample(Power2(-1)), (u: nat) => SampleTailRecursive(Power2(k - 1), u))(s);
        { RelateWithTailRecursive(k - 1, k, s); }
        Sample(Power2(k - 1))(s);
        { SampleEqualIfSameLog2Floor(n, Power2(k - 1), k, s); }
        Sample(n)(s);
      }
    }
  }

  // A version of Power(2, k) extended to negative k's.
  function Power2(k: int): nat {
    if k < 0 then 0 else if k == 0 then 1 else Power2(k - 1) * 2
  }

  lemma Power2Greater1(k: nat)
    ensures Power2(k) >= 1
  {}

  lemma Power2OfLog2(n: nat)
    ensures Power2(Helper.Log2(n) - 1) <= n < Power2(Helper.Log2(n))
  {}

  // All numbers between consecutive powers of 2 behave the same as arguments to SampleTailRecursive
  lemma SampleTailRecursiveEqualIfSameLog2Floor(m: nat, n: nat, k: nat, u: nat, s: RandomNumberGenerator.RNG)
    requires Power2(k - 1) <= m < Power2(k)
    requires Power2(k - 1) <= n < Power2(k)
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
    requires Power2(k - 1) <= m < Power2(k)
    requires Power2(k - 1) <= n < Power2(k)
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
  lemma RelateWithTailRecursive(k: nat, l: nat, s: RandomNumberGenerator.RNG)
    requires l <= k + 1
    decreases l
    ensures Monad.Bind(Sample(Power2(k - l)), (u: nat) => SampleTailRecursive(Power2(l - 1), u))(s) == Sample(Power2(k))(s)
  {
    if l == 0 {
      calc {
        Monad.Bind(Sample(Power2(k - l)), (u: nat) => SampleTailRecursive(Power2(l - 1), u))(s);
        (var (u, s') := Sample(Power2(k - l))(s); SampleTailRecursive(0, u)(s'));
        Sample(Power2(k))(s);
      }
    } else {
      var k' := k - l;
      assert Ineq1: Power2(l - 1) >= 1 by { Power2Greater1(l - 1); }
      assert Power2(k - l + 1) >= 1 by { Power2Greater1(k - l + 1); }
      calc {
        Monad.Bind(Sample(Power2(k - l)), (u: nat) => SampleTailRecursive(Power2(l - 1), u))(s);
        (var (u, s') := Sample(Power2(k - l))(s); SampleTailRecursive(Power2(l - 1), u)(s'));
        { reveal Ineq1; }
        (var (u, s') := Sample(Power2(k - l))(s);
         SampleTailRecursive(Power2(l - 1) / 2, if Monad.Head(s') then 2 * u + 1 else 2 * u)(Monad.Tail(s')));
        { assert Power2(k - l + 1) / 2 == Power2(k - l); }
        (var (u', s') := Monad.Bind(Sample(Power2(k - l)), UnifStep)(s);
         SampleTailRecursive(Power2(l - 2), u')(s'));
        (var (u', s') := Sample(Power2(k - l + 1))(s);
         SampleTailRecursive(Power2(l - 2), u')(s'));
        Monad.Bind(Sample(Power2(k - l + 1)), (u: nat) => SampleTailRecursive(Power2(l - 2), u))(s);
        { RelateWithTailRecursive(k, l - 1, s); }
        Sample(Power2(k))(s);
      }
    }
  }
}
