/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module MeasureTheory {
  /************
   Definitions
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0

  ghost predicate IsSigmaAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
    && (forall e | e in event_space :: e <= sample_space)
    && (iset{}) in event_space
    && (forall e | e in event_space :: (sample_space - e) in event_space)
    && (forall f: nat -> iset<T> | (forall n :: f(n) in event_space) :: (CountableUnion(f) in event_space))
  }

  ghost function CountableUnion<T(!new)>(f: nat -> iset<T>, i: nat := 0): iset<T> {
    iset n: nat | n >= i, x <- f(n) :: x
  }

  function CountableSum(f: nat -> real, i: nat := 0): real {
    assume {:axiom} false; // assume termination
    f(i) + CountableSum(f, i+1)
  }

  ghost const boolSampleSpace: iset<bool> := iset _: bool

  ghost const boolEventSpace: iset<iset<bool>> := iset _: iset<bool>

  ghost const natSampleSpace: iset<nat> := iset _: nat

  // The sigma algebra on the natural numbers is just the power set
  ghost const natEventSpace: iset<iset<nat>> := iset _: iset<nat>

  // Definition 5
  ghost predicate IsPositive<T(!new)>(event_space: iset<iset<T>>, mu: iset<T> -> real) {
    && mu(iset{}) == 0.0
    && forall e | e in event_space :: 0.0 <= mu(e)
  }

  // Definition 5
  ghost predicate IsAdditive<T(!new)>(event_space: iset<iset<T>>, mu: iset<T> -> real) {
    forall e1, e2 | e1 in event_space && e2 in event_space && e1 * e2 == iset{} :: mu(e1) + mu(e2) == mu(e1 + e2)
  }

  // Definition 5
  ghost predicate IsCountablyAdditive<T(!new)>(event_space: iset<iset<T>>, mu: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in event_space) && (forall m, n | m != n :: f(m) * f(n) == iset{}) && (CountableUnion(f) in event_space) :: (CountableSum((n: nat) => mu(f(n))) == mu(CountableUnion(f)))
  }

  // Definition 6
  ghost predicate IsMeasure<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    && IsSigmaAlgebra(event_space, sample_space)
    && IsPositive(event_space, mu)
    && IsCountablyAdditive(event_space, mu)
  }

  ghost function PreImage<S(!new),T>(f: S -> T, e: iset<T>): iset<S> {
    (iset s | f(s) in e)
  }

  // Definition 9
  ghost predicate IsMeasurable<S(!new),T>(event_space_s: iset<iset<S>>, event_space_t: iset<iset<T>>, f: S -> T) {
    forall e | e in event_space_t :: PreImage(f, e) in event_space_s
  }

  // Definition 10
  ghost predicate IsMeasurePreserving<S(!new),T>(event_space_s: iset<iset<S>>, mu_s: iset<S> -> real, event_space_t: iset<iset<T>>, mu_t: iset<T> -> real, f: S -> T) {
    && IsMeasurable(event_space_s, event_space_t, f)
    && forall e | e in event_space_t :: mu_s(PreImage(f, e)) == mu_t(e)
  }

  // Definition 12
  ghost predicate IsProbability<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    && IsMeasure(event_space, sample_space, mu)
    && mu(sample_space) == 1.0
  }

  // Definition 13
  predicate AreIndepEvents<T>(event_space: iset<iset<T>>, mu: iset<T> -> real, e1: iset<T>, e2: iset<T>) {
    && (e1 in event_space)
    && (e2 in event_space)
    && (mu(e1 * e2) == mu(e1) * mu(e2))
  }

  /*******
   Lemmas
  *******/

  lemma boolsHaveSigmaAlgebra()
    ensures IsSigmaAlgebra(boolEventSpace, boolSampleSpace)
  {
    forall e | e in boolEventSpace ensures e <= boolSampleSpace {
      assert e <= boolSampleSpace by {
        forall x: bool ensures x in e ==> x in boolSampleSpace {}
      }
    }
  }

  lemma natsHaveSigmaAlgebra()
    ensures IsSigmaAlgebra(natEventSpace, natSampleSpace)
  {}

  lemma PreImageIdentity<S(!new)>(f: S -> S, e: iset<S>)
    requires forall s: S :: f(s) == s
    ensures PreImage(f, e) == e
  {}

  lemma PreImagesEqual<S(!new),T,U>(f: S -> T, e: iset<T>, f': S -> U, e': iset<U>)
    requires forall s: S :: f(s) in e <==> f'(s) in e'
    ensures PreImage(f, e) == PreImage(f', e')
  {}

  // Equation (2.18)
  lemma PosCountAddImpliesAdd<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real)
    requires IsSigmaAlgebra(event_space, sample_space)
    requires IsPositive(event_space, mu)
    requires IsCountablyAdditive(event_space, mu)
    ensures IsAdditive(event_space, mu)
  {
    forall e1, e2 | e1 in event_space && e2 in event_space && e1 * e2 == iset{} ensures mu(e1) + mu(e2) == mu(e1 + e2) {
      var f : nat -> iset<T> := (n: nat) => if n == 0 then e1 else if n == 1 then e2 else iset{};
      assert CountableUnion(f) == e1 + e2;
      assert CountableSum((n: nat) => mu(f(n))) == mu(e1) + mu(e2) by {
        assert CountableSum((n: nat) => mu(f(n)), 2) == 0.0 by {
          CountableSumOfZeroesIsZero((n: nat) => mu(f(n)), 2);
        }
        calc {
          CountableSum((n: nat) => mu(f(n)))
       ==
          mu(f(0)) + CountableSum((n: nat) => mu(f(n)), 1)
       ==
          mu(f(0)) + mu(f(1)) + CountableSum((n: nat) => mu(f(n)), 2)
       ==
          mu(e1) + mu(e2) + CountableSum((n: nat) => mu(f(n)), 2)
       ==
          mu(e1) + mu(e2);
        }
      }
      assert mu(CountableUnion(f)) == CountableSum((n: nat) => mu(f(n))) by {
        assert IsCountablyAdditive(event_space, mu);
      }
      assert mu(e1 + e2) == mu(e1) + mu(e2);
    }
  }

  lemma {:axiom} CountableSumOfZeroesIsZero(f: nat -> real, i: nat := 0)
    requires forall n | n >= i :: f(n) == 0.0
    ensures CountableSum(f, i) == 0.0

  lemma CountableUnionSplit<T(!new)>(f: nat -> iset<T>, i: nat)
    ensures CountableUnion(f, i) == f(i) + CountableUnion(f, i + 1)
  {}

  lemma BinaryUnion<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, e1: iset<T>, e2: iset<T>)
    requires IsSigmaAlgebra(event_space, sample_space)
    requires e1 in event_space
    requires e2 in event_space
    ensures e1 + e2 in event_space
  {
    var f : nat -> iset<T> := (n: nat) => if n == 0 then e1 else if n == 1 then e2 else iset{};
    assert CountableUnion(f) == e1 + e2 by {
      calc {
        CountableUnion(f);
      == { CountableUnionSplit(f, 0); }
        e1 + CountableUnion(f, 1);
      == { CountableUnionSplit(f, 1); }
        e1 + e2;
      }
    }
  }
}
