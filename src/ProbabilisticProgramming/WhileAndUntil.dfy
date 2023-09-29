/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "Monad.dfy"
include "Quantifier.dfy"
include "Independence.dfy"
include "RandomNumberGenerator.dfy"

module WhileAndUntil {
  import Monad
  import Quantifier
  import Independence
  import RandomNumberGenerator

  /************
   Definitions  
  ************/

  // Definition 37
  function ProbWhileCut<A>(c: A -> bool, b: A -> Monad.Hurd<A>, n: nat, a: A): Monad.Hurd<A> {
    if n == 0 then
      Monad.Return(a)
    else (
           if c(a) then
             Monad.Bind(b(a), (a': A) => ProbWhileCut(c, b, n-1, a'))
           else
             Monad.Return(a)
         )
  }

  // Definition 39 / True iff mu(iset s | ProbWhile(c, b, a)(s) terminates) == 1
  ghost predicate ProbWhileTerminates<A(!new)>(b: A -> Monad.Hurd<A>, c: A -> bool) {
    var P := (a: A) =>
               (s: RandomNumberGenerator.RNG) => exists n :: !c(ProbWhileCut(c, b, n, a)(s).0);
    forall a :: Quantifier.ForAllStar(P(a))
  }

  // Theorem 38
  function ProbWhile<A>(c: A -> bool, b: A -> Monad.Hurd<A>, a: A): (f: Monad.Hurd<A>)
    requires ProbWhileTerminates(b, c)
  {
    assume {:axiom} false;
    if c(a) then
      Monad.Bind(b(a), (a': A) => ProbWhile(c, b, a'))
    else
      Monad.Return(a)
  }

  method ProbWhileImperative<A>(c: A -> bool, b: A -> Monad.Hurd<A>, a: A, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbWhileTerminates(b, c)
    ensures ProbWhile(c, b, a)(s) == t
    decreases *
  {
    while c(a)
      decreases *
    {
      var (a, s) := b(a)(s);
    }
    return (a, s);
  }

  method ProbWhileImperativeAlternative<A>(c: A -> bool, b: A -> Monad.Hurd<A>, a: A, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbWhileTerminates(b, c)
    ensures ProbWhile(c, b, a)(s) == t
    decreases *
  {
    while true
      decreases *
    {
      if !c(a) {
        return (a, s);
      } else {
        var (a, s) := b(a)(s);
      }
    }
  }

  ghost predicate ProbUntilTerminates<A(!new)>(b: Monad.Hurd<A>, c: A -> bool) {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    ProbWhileTerminates(b', c')
  }

  // Definition 44
  function ProbUntil<A>(b: Monad.Hurd<A>, c: A -> bool): (f: Monad.Hurd<A>)
    requires ProbUntilTerminates(b, c)
    ensures
      var c' := (a: A) => !c(a);
      var b' := (a: A) => b;
      forall s :: f(s) == ProbWhile(c', b', b(s).0)(b(s).1)
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    Monad.Bind(b, (a: A) => ProbWhile(c', b', a))
  }

  method ProbUntilImperative<A>(b: Monad.Hurd<A>, c: A -> bool, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbUntilTerminates(b, c)
    ensures t == ProbUntil(b, c)(s)
    decreases *
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    t := ProbWhileImperative(c', b', b(s).0, b(s).1);
  }

  function Helper<A(!new)>(b: A -> Monad.Hurd<A>, c: A -> bool, a: A): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      !c(b(a)(s).0)
  }

  function Helper2<A(!new)>(b: Monad.Hurd<A>, c: A -> bool): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      c(b(s).0)
  }

  function Helper3<A>(b: Monad.Hurd<A>, c: A -> bool): (RandomNumberGenerator.RNG -> bool)
    requires ProbUntilTerminates(b, c)
  {
    (s: RandomNumberGenerator.RNG) =>
      c(ProbUntil(b, c)(s).0)
  }

  ghost function ConstructEvents<A>(b: Monad.Hurd<A>, c: A -> bool, d: A -> bool): (x: (iset<RandomNumberGenerator.RNG>, iset<RandomNumberGenerator.RNG>, iset<RandomNumberGenerator.RNG>))
    requires ProbUntilTerminates(b, c)
  {
    (iset s | d(ProbUntil(b, c)(s).0), iset s | d(b(s).0) && c(b(s).0), iset s | c(b(s).0))
  }

  /*******
   Lemmas  
  *******/

  lemma EnsureProbUntilTerminates<A(!new)>(b: Monad.Hurd<A>, c: A -> bool)
    requires Independence.IsIndepFn(b)
    requires Quantifier.ExistsStar((s: RandomNumberGenerator.RNG) => c(b(s).0))
    ensures ProbUntilTerminates(b, c)
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    var p := (s: RandomNumberGenerator.RNG) => c(b(s).0);
    assert ProbUntilTerminates(b, c) by {
      forall a: A ensures Independence.IsIndepFn(b'(a)) {
        assert b'(a) == b;
      }
      forall a: A ensures Quantifier.ExistsStar(Helper(b', c', a)) {
        assert Quantifier.ExistsStar(p);
        assert (iset s | p(s)) == (iset s | Helper(b', c', a)(s));
      }
      assert ProbWhileTerminates(b', c') by {
        EnsureProbWhileTerminates(b', c');
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureProbWhileTerminates<A(!new)>(b: A -> Monad.Hurd<A>, c: A -> bool)
    requires forall a :: Independence.IsIndepFn(b(a))
    requires forall a :: Quantifier.ExistsStar(Helper(b, c, a))
    ensures ProbWhileTerminates(b, c)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} ProbUntilProbabilityFraction<A>(b: Monad.Hurd<A>, c: A -> bool, d: A -> bool)
    requires Independence.IsIndepFn(b)
    requires Quantifier.ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures
      var x := ConstructEvents(b, c, d);
      && x.0 in RandomNumberGenerator.event_space
      && x.1 in RandomNumberGenerator.event_space
      && x.2 in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(x.2) != 0.0
      && RandomNumberGenerator.mu(x.0) == RandomNumberGenerator.mu(x.1) / RandomNumberGenerator.mu(x.2)

  // Equation (3.39)
  lemma {:axiom} ProbUntilAsBind<A(!new)>(b: Monad.Hurd<A>, c: A -> bool, s: RandomNumberGenerator.RNG)
    requires Independence.IsIndepFn(b)
    requires Quantifier.ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures ProbUntil(b, c) == Monad.Bind(b, (x: A) => if c(x) then Monad.Return(x) else ProbUntil(b, c))

  // Equation (3.40)
  lemma EnsureProbUntilTerminatesAndForAll<A(!new)>(b: Monad.Hurd<A>, c: A -> bool)
    requires Independence.IsIndepFn(b)
    requires Quantifier.ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures Quantifier.ForAllStar(Helper3(b, c))
  {
    EnsureProbUntilTerminates(b, c);
    assume {:axiom} Quantifier.ForAllStar(Helper3(b, c));
  }
}