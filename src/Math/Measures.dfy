/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Measures {
  import Series

  /************
   Definitions
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0

  // States that given collection of sets is σ-algebra on the set of values of type `T`.
  // In other words, the sample space is `SampleSpace<T>()`, i.e. the set of all values of type `T`,
  // and `eventSpace` is the collection of measurable subsets.
  ghost predicate IsSigmaAlgebra<T(!new)>(eventSpace: iset<iset<T>>) {
    && (iset{}) in eventSpace
    && (forall e | e in eventSpace :: Complement(e) in eventSpace)
    && (forall f: nat -> iset<T> | (forall n :: f(n) in eventSpace) :: (CountableUnion(f) in eventSpace))
  }

  // The set of all values of type `T` that are not in the given set.
  ghost function Complement<T(!new)>(event: iset<T>): iset<T> {
    iset x: T | x !in event
  }

  // The set of all values of type `T`.
  ghost function SampleSpace<T(!new)>(): iset<T> {
    Complement(iset{})
  }

  ghost function CountableUnion<T(!new)>(f: nat -> iset<T>, i: nat := 0): iset<T> {
    iset n: nat | n >= i, x <- f(n) :: x
  }

  // The σ-algebra that contains all subsets.
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

  ghost predicate PairwiseDisjoint<T(!new)>(s: nat -> iset<T>) {
    forall m, n | m != n :: s(m) * s(n) == iset{}
  }

  // Definition 5
  ghost predicate IsCountablyAdditive<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in eventSpace) && PairwiseDisjoint(f) && (CountableUnion(f) in eventSpace) :: Series.SumsTo((n: nat) => Prob(f(n)), Prob(CountableUnion(f)))
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

  lemma {:axiom} ProbabilityLe1<T>(event: iset<T>, eventSpace: iset<iset<T>>, prob: iset<T> -> real)
    requires IsProbability(eventSpace, prob)
    requires event in eventSpace
    ensures 0.0 <= prob(event) <= 1.0

  lemma {:axiom} IsMonotonic<T>(eventSpace: iset<iset<T>>, mu: iset<T> -> real, set1: iset<T>, set2: iset<T>)
    requires IsMeasure(eventSpace, mu)
    requires set1 in eventSpace
    requires set2 in eventSpace
    requires set1 <= set2
    ensures mu(set1) <= mu(set2)

  lemma MeasureOfDisjointUnionIsSum<T(!new)>(eventSpace: iset<iset<T>>, mu: iset<T> -> real, set1: iset<T>, set2: iset<T>)
    requires IsMeasure(eventSpace, mu)
    requires set1 in eventSpace
    requires set2 in eventSpace
    requires set1 * set2 == iset{}
    ensures mu(set1 + set2) == mu(set1) + mu(set2)
  {
    assert IsAdditive(eventSpace, mu) by {
      PosCountAddImpliesAdd(eventSpace, mu);
    }
  }

  lemma MeasureOfCountableDisjointUnionIsSum<T(!new)>(eventSpace: iset<iset<T>>, mu: iset<T> -> real, parts: nat -> iset<T>, muParts: nat -> real)
    requires IsMeasure(eventSpace, mu)
    requires forall n: nat :: parts(n) in eventSpace
    requires PairwiseDisjoint(parts)
    requires forall n: nat :: muParts(n) == mu(parts(n))
    ensures Series.SumsTo(muParts, mu(CountableUnion(parts)))
  {
    assert Series.SumsTo((n: nat) => mu(parts(n)), mu(CountableUnion(parts)));
    Series.SumOfEqualsIsEqual((n: nat) => mu(parts(n)), muParts, mu(CountableUnion(parts)));
  }

  // Equation (2.18)
  lemma PosCountAddImpliesAdd<T(!new)>(eventSpace: iset<iset<T>>, Prob: iset<T> -> real)
    requires IsSigmaAlgebra(eventSpace)
    requires IsPositive(eventSpace, Prob)
    requires IsCountablyAdditive(eventSpace, Prob)
    ensures IsAdditive(eventSpace, Prob)
  {
    forall e1, e2 | e1 in eventSpace && e2 in eventSpace && e1 * e2 == iset{} ensures Prob(e1) + Prob(e2) == Prob(e1 + e2) {
      var f : nat -> iset<T> := (n: nat) => if n == 0 then e1 else if n == 1 then e2 else iset{};
      assert CountableUnion(f) == e1 + e2 by {
        calc {
          CountableUnion(f);
          f(0) + f(1);
          e1 + e2;
        }
      }
      var probs := (n: nat) => Prob(f(n));
      var probSum := Prob(e1) + Prob(e2);
      assert Series.SumsTo(probs, probSum) by {
        assert seq(2, probs) == [probs(0), probs(1)];
        calc {
          Series.PartialSums(probs)(2);
          Series.SumTo(probs, 2);
          probs(0) + Series.SumFromTo(probs, 1, 2);
          probs(0) + probs(1) + Series.SumFromTo(probs, 2, 2);
          Prob(e1) + Prob(e2);
        }
        Series.ZeroSuffixSum(probs, 2, Prob(e1) + Prob(e2));
      }
      assert Series.SumsTo(probs, Prob(CountableUnion(f))) by {
        assert IsCountablyAdditive(eventSpace, Prob);
      }
      Series.SumsToImpliesSumIs(probs, probSum);
      Series.SumsToImpliesSumIs(probs, Prob(CountableUnion(f)));
      assert Prob(e1 + e2) == Prob(e1) + Prob(e2);
    }
  }

  lemma CountableUnionSplit<T(!new)>(f: nat -> iset<T>, i: nat)
    ensures CountableUnion(f, i) == f(i) + CountableUnion(f, i + 1)
  {}

  lemma BinaryUnionIsMeasurable<T(!new)>(eventSpace: iset<iset<T>>, e1: iset<T>, e2: iset<T>)
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

  lemma BinaryIntersectionIsMeasurable<T(!new)>(eventSpace: iset<iset<T>>, e1: iset<T>, e2: iset<T>)
    requires IsSigmaAlgebra(eventSpace)
    requires e1 in eventSpace
    requires e2 in eventSpace
    ensures e1 * e2 in eventSpace
  {
    assert Complement(e1) + Complement(e2) in eventSpace by {
      assert Complement(e1) in eventSpace;
      assert Complement(e2) in eventSpace;
      BinaryUnionIsMeasurable(eventSpace, Complement(e1), Complement(e2));
    }
    assert Complement(Complement(e1) + Complement(e2)) in eventSpace;
    assert e1 * e2 == Complement(Complement(e1) + Complement(e2));
  }

}
