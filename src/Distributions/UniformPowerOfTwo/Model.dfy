/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Model {
  import Helper
  import Rand
  import Quantifier
  import Monad
  import Independence
  import Loops
  import NatArith

  /************
   Definitions
  ************/

  // Adapted from Definition 48 (see issue #79 for the reason of the modification)
  // The return value u is uniformly distributed between 0 <= u < 2^k where 2^k <= n < 2^(k + 1).
  opaque function Sample(n: nat): (h: Monad.Hurd<nat>)
    requires n >= 1
    ensures forall s :: Sample(n)(s).Result? // always terminates, not just almost surely
  {
    if n == 1 then
      Monad.Return(0)
    else
      Monad.Bind(Sample(n/2), UnifStep)
  }

  function UnifStepHelper(m: nat): bool -> Monad.Hurd<nat> {
    (b: bool) => Monad.Return(if b then 2*m + 1 else 2*m)
  }

  function UnifStep(m: nat): Monad.Hurd<nat> {
    Monad.Bind(Monad.Coin, UnifStepHelper(m))
  }


  // A tail recursive version of Sample
  function SampleTailRecursive(n: nat, u: nat := 0): Monad.Hurd<nat>
    requires n >= 1
  {
    (s: Rand.Bitstream) =>
      if n == 1 then
        Monad.Result(u, s)
      else
        SampleTailRecursive(n / 2, if Rand.Head(s) then 2*u + 1 else 2*u)(Rand.Tail(s))
  }

  /*******
   Lemmas
  *******/

  // Equivalence of Sample and its tail-recursive version
  lemma SampleCorrespondence(n: nat, s: Rand.Bitstream)
    requires n >= 1
    ensures SampleTailRecursive(n)(s) == Sample(n)(s)
  {
    if n == 1 {
      reveal Sample();
      assert SampleTailRecursive(n)(s) == Sample(n)(s);
    } else {
      var k := NatArith.Log2Floor(n);
      assert NatArith.Power(2, k) <= n < NatArith.Power(2, k + 1) by { NatArith.Power2OfLog2Floor(n); }
      calc {
        SampleTailRecursive(n)(s);
        { SampleTailRecursiveEqualIfSameLog2Floor(n, NatArith.Power(2, k), k, 0, s); }
        SampleTailRecursive(NatArith.Power(2, k))(s);
        Monad.Bind(Sample(NatArith.Power(2, 0)), (u: nat) => SampleTailRecursive(NatArith.Power(2, k), u))(s);
        { RelateWithTailRecursive(k, 0, s); }
        Sample(NatArith.Power(2, k))(s);
        { SampleEqualIfSameLog2Floor(n, NatArith.Power(2, k), k, s); }
        Sample(n)(s);
      }
    }
  }

  // All numbers between consecutive powers of 2 behave the same as arguments to SampleTailRecursive
  lemma SampleTailRecursiveEqualIfSameLog2Floor(m: nat, n: nat, k: nat, u: nat, s: Rand.Bitstream)
    requires m >= 1
    requires n >= 1
    requires NatArith.Power(2, k) <= m < NatArith.Power(2, k + 1)
    requires NatArith.Power(2, k) <= n < NatArith.Power(2, k + 1)
    ensures SampleTailRecursive(m, u)(s) == SampleTailRecursive(n, u)(s)
  {
    if k == 0 {
      assert m == n;
    } else {
      assert 1 <= m;
      assert 1 <= n;
      calc {
        SampleTailRecursive(m, u)(s);
        SampleTailRecursive(m / 2, if Rand.Head(s) then 2*u + 1 else 2*u)(Rand.Tail(s));
        { SampleTailRecursiveEqualIfSameLog2Floor(m / 2, n / 2, k - 1, if Rand.Head(s) then 2*u + 1 else 2*u, Rand.Tail(s)); }
        SampleTailRecursive(n / 2, if Rand.Head(s) then 2*u + 1 else 2*u)(Rand.Tail(s));
        SampleTailRecursive(n, u)(s);
      }
    }
  }

  // All numbers between consecutive powers of 2 behave the same as arguments to Sample
  lemma SampleEqualIfSameLog2Floor(m: nat, n: nat, k: nat, s: Rand.Bitstream)
    requires m >= 1
    requires n >= 1
    requires NatArith.Power(2, k) <= m < NatArith.Power(2, k + 1)
    requires NatArith.Power(2, k) <= n < NatArith.Power(2, k + 1)
    ensures Sample(m)(s) == Sample(n)(s)
  {
    if k == 0 {
      assert m == n;
    } else {
      assert 1 <= m;
      assert 1 <= n;
      calc {
        Sample(m)(s);
        { reveal Sample(); }
        Monad.Bind(Sample(m / 2), UnifStep)(s);
        { SampleEqualIfSameLog2Floor(m / 2, n / 2, k - 1, s); }
        Monad.Bind(Sample(n / 2), UnifStep)(s);
        { reveal Sample(); }
        Sample(n)(s);
      }
    }
  }

  // The induction invariant for the equivalence proof (generalized version of SampleCorrespondence)
  lemma RelateWithTailRecursive(l: nat, m: nat, s: Rand.Bitstream)
    decreases l
    ensures Monad.Bind(Sample(NatArith.Power(2, m)), (u: nat) => SampleTailRecursive(NatArith.Power(2, l), u))(s) == Sample(NatArith.Power(2, m + l))(s)
  {
    if l == 0 {
      calc {
        Monad.Bind(Sample(NatArith.Power(2, m)), (u: nat) => SampleTailRecursive(NatArith.Power(2, l), u))(s);
        (var Result(u, s') := Sample(NatArith.Power(2, m))(s); SampleTailRecursive(1, u)(s'));
        Sample(NatArith.Power(2, m + l))(s);
      }
    } else {
      assert LGreaterZero: NatArith.Power(2, l) >= 1 by { NatArith.PowerGreater0(2, l); }
      assert MGreaterZero: NatArith.Power(2, m) >= 1 by { NatArith.PowerGreater0(2, m); }
      assert L1GreaterZero: NatArith.Power(2, l - 1) >= 1 by { NatArith.PowerGreater0(2, l - 1); }
      calc {
        Monad.Bind(Sample(NatArith.Power(2, m)), (u: nat) => SampleTailRecursive(NatArith.Power(2, l), u))(s);
        (var Result(u, s') := Sample(NatArith.Power(2, m))(s); SampleTailRecursive(NatArith.Power(2, l), u)(s'));
        { reveal LGreaterZero; }
        (var Result(u, s') := Sample(NatArith.Power(2, m))(s);
         SampleTailRecursive(NatArith.Power(2, l) / 2, if Rand.Head(s') then 2 * u + 1 else 2 * u)(Rand.Tail(s')));
        { assert NatArith.Power(2, l) / 2 == NatArith.Power(2, l - 1); reveal L1GreaterZero; }
        (var Result(u', s') := Monad.Bind(Sample(NatArith.Power(2, m)), UnifStep)(s);
         SampleTailRecursive(NatArith.Power(2, l - 1), u')(s'));
        { assert NatArith.Power(2, m + 1) / 2 == NatArith.Power(2, m); reveal Sample(); }
        (var Result(u', s') := Sample(NatArith.Power(2, m + 1))(s);
         SampleTailRecursive(NatArith.Power(2, l - 1), u')(s'));
        Monad.Bind(Sample(NatArith.Power(2, m + 1)), (u: nat) => SampleTailRecursive(NatArith.Power(2, l - 1), u))(s);
        { RelateWithTailRecursive(l - 1, m + 1, s); }
        Sample(NatArith.Power(2, m + l))(s);
      }
    }
  }
}
