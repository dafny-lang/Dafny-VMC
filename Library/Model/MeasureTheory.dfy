module MeasureTheory {
  /************
   Definitions  
  ************/

  ghost predicate IsSigmaAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
    && (forall e | e in event_space :: e <= sample_space)
    && (iset{}) in event_space
    && (forall e | e in event_space :: (sample_space - e) in event_space)
  }

  ghost function CountableUnion<T>(f: nat -> iset<T>, i: nat := 0): iset<T> {
    assume {:axiom} false;
    f(i) + CountableUnion(f, i+1)
  }

  ghost function CountableSum(f: nat -> real, i: nat := 0): real {
    assume {:axiom} false;
    f(i) + CountableSum(f, i+1)
  }

  // Definition 5
  ghost predicate IsPositive<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    && mu(iset{}) == 0.0
    && forall e | e in event_space :: 0.0 <= mu(e)
  }

  // Definition 5
  ghost predicate IsAdditive<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    forall e1, e2 | e1 in event_space && e2 in event_space && e1 * e2 == iset{} :: mu(e1) + mu(e2) == mu(e1 + e2)
  }

  // Definition 5
  ghost predicate IsCountablyAdditive<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in event_space) && (forall m, n | m != n :: f(m) * f(n) == iset{}) && (CountableUnion(f) in event_space) :: (CountableSum((n: nat) => mu(f(n))) == mu(CountableUnion(f)))
  }

  // Definition 6 & Definition 12
  ghost predicate IsMeasure<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real) {
    && IsSigmaAlgebra(event_space, sample_space)
    && IsPositive(event_space, sample_space, mu)
    && IsCountablyAdditive(event_space, sample_space, mu)
    && mu(sample_space) == 1.0
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

  // Definition 13
  ghost predicate AreIndepEvents<T>(event_space: iset<iset<T>>, mu: iset<T> -> real, e1: iset<T>, e2: iset<T>) {
    && (e1 in event_space)
    && (e2 in event_space)
    && (mu(e1 * e2) == mu(e1) * mu(e2))
  }

  /*******
   Lemmas  
  *******/

  // Equation (2.18)
  lemma {:axiom} LemmaPosCountAddImpliesAdd<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>, mu: iset<T> -> real)
    requires IsPositive(event_space, sample_space, mu)
    requires IsCountablyAdditive(event_space, sample_space, mu)
    ensures IsAdditive(event_space, sample_space, mu)

}