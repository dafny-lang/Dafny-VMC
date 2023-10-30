/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module UniformPowerOfTwo.Equivalence {
  import Rand
  import Monad
  import Helper
  import Model

  /************
   Definitions
  ************/

  // A tail recursive version of Sample, closer to the imperative implementation
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
    ensures SampleTailRecursive(n)(s) == Model.Sample(n)(s)
  {
    if n == 1 {
      reveal Model.Sample();
      assert SampleTailRecursive(n)(s) == Model.Sample(n)(s);
    } else {
      var k := Helper.Log2Floor(n);
      assert Helper.Power(2, k) <= n < Helper.Power(2, k + 1) by { Helper.Power2OfLog2Floor(n); }
      calc {
        SampleTailRecursive(n)(s);
        { SampleTailRecursiveEqualIfSameLog2Floor(n, Helper.Power(2, k), k, 0, s); }
        SampleTailRecursive(Helper.Power(2, k))(s);
        Monad.Bind(Model.Sample(Helper.Power(2, 0)), (u: nat) => SampleTailRecursive(Helper.Power(2, k), u))(s);
        { RelateWithTailRecursive(k, 0, s); }
        Model.Sample(Helper.Power(2, k))(s);
        { SampleEqualIfSameLog2Floor(n, Helper.Power(2, k), k, s); }
        Model.Sample(n)(s);
      }
    }
  }

  // All numbers between consecutive powers of 2 behave the same as arguments to SampleTailRecursive
  lemma SampleTailRecursiveEqualIfSameLog2Floor(m: nat, n: nat, k: nat, u: nat, s: Rand.Bitstream)
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
    requires Helper.Power(2, k) <= m < Helper.Power(2, k + 1)
    requires Helper.Power(2, k) <= n < Helper.Power(2, k + 1)
    ensures Model.Sample(m)(s) == Model.Sample(n)(s)
  {
    if k == 0 {
      assert m == n;
    } else {
      assert 1 <= m;
      assert 1 <= n;
      calc {
        Model.Sample(m)(s);
        { reveal Model.Sample(); }
        Monad.Bind(Model.Sample(m / 2), Model.UnifStep)(s);
        { SampleEqualIfSameLog2Floor(m / 2, n / 2, k - 1, s); }
        Monad.Bind(Model.Sample(n / 2), Model.UnifStep)(s);
        { reveal Model.Sample(); }
        Model.Sample(n)(s);
      }
    }
  }

  // The induction invariant for the equivalence proof (generalized version of SampleCorrespondence)
  lemma RelateWithTailRecursive(l: nat, m: nat, s: Rand.Bitstream)
    decreases l
    ensures Monad.Bind(Model.Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s) == Model.Sample(Helper.Power(2, m + l))(s)
  {
    if l == 0 {
      calc {
        Monad.Bind(Model.Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s);
        (var Result(u, s') := Model.Sample(Helper.Power(2, m))(s); SampleTailRecursive(1, u)(s'));
        Model.Sample(Helper.Power(2, m + l))(s);
      }
    } else {
      assert LGreaterZero: Helper.Power(2, l) >= 1 by { Helper.PowerGreater0(2, l); }
      assert MGreaterZero: Helper.Power(2, m) >= 1 by { Helper.PowerGreater0(2, m); }
      assert L1GreaterZero: Helper.Power(2, l - 1) >= 1 by { Helper.PowerGreater0(2, l - 1); }
      calc {
        Monad.Bind(Model.Sample(Helper.Power(2, m)), (u: nat) => SampleTailRecursive(Helper.Power(2, l), u))(s);
        (var Result(u, s') := Model.Sample(Helper.Power(2, m))(s); SampleTailRecursive(Helper.Power(2, l), u)(s'));
        { reveal LGreaterZero; }
        (var Result(u, s') := Model.Sample(Helper.Power(2, m))(s);
         SampleTailRecursive(Helper.Power(2, l) / 2, if Rand.Head(s') then 2 * u + 1 else 2 * u)(Rand.Tail(s')));
        { assert Helper.Power(2, l) / 2 == Helper.Power(2, l - 1); reveal L1GreaterZero; }
        (var Result(u', s') := Monad.Bind(Model.Sample(Helper.Power(2, m)), Model.UnifStep)(s);
         SampleTailRecursive(Helper.Power(2, l - 1), u')(s'));
        { assert Helper.Power(2, m + 1) / 2 == Helper.Power(2, m); reveal Model.Sample(); }
        (var Result(u', s') := Model.Sample(Helper.Power(2, m + 1))(s);
         SampleTailRecursive(Helper.Power(2, l - 1), u')(s'));
        Monad.Bind(Model.Sample(Helper.Power(2, m + 1)), (u: nat) => SampleTailRecursive(Helper.Power(2, l - 1), u))(s);
        { RelateWithTailRecursive(l - 1, m + 1, s); }
        Model.Sample(Helper.Power(2, m + l))(s);
      }
    }
  }

}
