/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Measures {
  /************
   Definitions
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0

  ghost function Complement<T(!new)>(event: iset<T>): iset<T> {
    iset x: T | x !in event
  }

  ghost function SampleSpace<T(!new)>(): iset<T> {
    Complement(iset{})
  }

  ghost predicate IsSigmaAlgebra<T(!new)>(eventSpace: iset<iset<T>>) {
    && (iset{}) in eventSpace
    && (forall e | e in eventSpace :: Complement(e) in eventSpace)
    && (forall f: nat -> iset<T> | (forall n :: f(n) in eventSpace) :: (CountableUnion(f) in eventSpace))
  }

  ghost function CountableUnion<T(!new)>(f: nat -> iset<T>, i: nat := 0): iset<T> {
    iset n: nat | n >= i, x <- f(n) :: x
  }

  function CountableSum(f: nat -> real, i: nat := 0): real {
    assume {:axiom} false; // assume termination
    f(i) + CountableSum(f, i+1)
  }

  ghost function DiscreteSigmaAlgebra<A(!new)>(): iset<iset<A>> {
    iset _: iset<A>
  }

  ghost const boolEventSpace: iset<iset<bool>> := DiscreteSigmaAlgebra<bool>()

  // The sigma algebra on the natural numbers is just the power set
  ghost const natEventSpace: iset<iset<nat>> := DiscreteSigmaAlgebra<nat>()

  // Definition 5
  ghost predicate IsPositive<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    && Prob(iset{}) == 0.0
    && forall e | e in eventSpace :: 0.0 <= Prob(e)
  }

  // Definition 5
  ghost predicate IsAdditive<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    forall e1, e2 | e1 in eventSpace && e2 in eventSpace && e1 * e2 == iset{} :: Prob(e1) + Prob(e2) == Prob(e1 + e2)
  }

  // Definition 5
  ghost predicate IsCountablyAdditive<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in eventSpace) && (forall m, n | m != n :: f(m) * f(n) == iset{}) && (CountableUnion(f) in eventSpace) :: (CountableSum((n: nat) => Prob(f(n))) == Prob(CountableUnion(f)))
  }

  // Definition 6
  ghost predicate IsMeasure<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    && IsSigmaAlgebra(eventSpace)
    && IsPositive(eventSpace, Prob)
    && IsCountablyAdditive(eventSpace, Prob)
  }

  ghost function PreImage<S(!new),T>(f: S -> T, e: iset<T>): iset<S> {
    (iset s | f(s) in e)
  }

  // Definition 9
  ghost predicate IsMeasurable<S(!new),T>(eventSpaceS: iset<iset<S>>, eventSpaceT: iset<iset<T>>, f: S -> T) {
    forall e | e in eventSpaceT :: PreImage(f, e) in eventSpaceS
  }

  // Definition 10
  ghost predicate IsMeasurePreserving<S(!new),T>(eventSpaceS: iset<iset<S>>, measureS: iset<S> -> real, eventSpaceT: iset<iset<T>>, measureT: iset<T> -> real, f: S -> T) {
    && IsMeasurable(eventSpaceS, eventSpaceT, f)
    && forall e | e in eventSpaceT :: measureS(PreImage(f, e)) == measureT(e)
  }

  // Definition 12
  ghost predicate IsProbability<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    && IsMeasure(eventSpace, Prob)
    && Prob(SampleSpace()) == 1.0
  }

  // Definition 13
  predicate AreIndepEvents<T>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real, e1: iset<T>, e2: iset<T>) {
    && (e1 in eventSpace)
    && (e2 in eventSpace)
    && (Prob(e1 * e2) == Prob(e1) * Prob(e2))
  }

  /*******
   Lemmas
  *******/

  lemma boolsHaveSigmaAlgebra()
    ensures IsSigmaAlgebra(boolEventSpace)
  {}

  lemma natsHaveSigmaAlgebra()
    ensures IsSigmaAlgebra(natEventSpace)
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
  lemma PosCountAddImpliesAdd<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real)
    requires IsSigmaAlgebra(eventSpace)
    requires IsPositive(eventSpace, Prob)
    requires IsCountablyAdditive(eventSpace, Prob)
    ensures IsAdditive(eventSpace, Prob)
  {
    forall e1, e2 | e1 in eventSpace && e2 in eventSpace && e1 * e2 == iset{} ensures Prob(e1) + Prob(e2) == Prob(e1 + e2) {
      var f : nat -> iset<T> := (n: nat) => if n == 0 then e1 else if n == 1 then e2 else iset{};
      assert CountableUnion(f) == e1 + e2;
      assert CountableSum((n: nat) => Prob(f(n))) == Prob(e1) + Prob(e2) by {
        assert CountableSum((n: nat) => Prob(f(n)), 2) == 0.0 by {
          CountableSumOfZeroesIsZero((n: nat) => Prob(f(n)), 2);
        }
        calc {
          CountableSum((n: nat) => Prob(f(n)))
       ==
          Prob(f(0)) + CountableSum((n: nat) => Prob(f(n)), 1)
       ==
          Prob(f(0)) + Prob(f(1)) + CountableSum((n: nat) => Prob(f(n)), 2)
       ==
          Prob(e1) + Prob(e2) + CountableSum((n: nat) => Prob(f(n)), 2)
       ==
          Prob(e1) + Prob(e2);
        }
      }
      assert Prob(CountableUnion(f)) == CountableSum((n: nat) => Prob(f(n))) by {
        assert IsCountablyAdditive(eventSpace, Prob);
      }
      assert Prob(e1 + e2) == Prob(e1) + Prob(e2);
    }
  }

  lemma {:axiom} CountableSumOfZeroesIsZero(f: nat -> real, i: nat := 0)
    requires forall n | n >= i :: f(n) == 0.0
    ensures CountableSum(f, i) == 0.0

  lemma CountableUnionSplit<T(!new)>(f: nat -> iset<T>, i: nat)
    ensures CountableUnion(f, i) == f(i) + CountableUnion(f, i + 1)
  {}

  lemma BinaryUnion<T(!new)>(eventSpace: iset<iset<T>>, e1: iset<T>, e2: iset<T>)
    requires IsSigmaAlgebra(eventSpace)
    requires e1 in eventSpace
    requires e2 in eventSpace
    ensures e1 + e2 in eventSpace
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
