/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Monad.dfy"
include "Quantifier.dfy"
include "Independence.dfy"
include "RandomNumberGenerator.dfy"

module WhileAndUntil {
  import opened Monad
  import opened Quantifier
  import opened Independence
  import opened RandomNumberGenerator

  /************
   Definitions  
  ************/

  // Definition 37
  function ProbWhileCut<A>(c: A -> bool, b: A -> Hurd<A>, n: nat, a: A): Hurd<A> {
    if n == 0 then
      Return(a)
    else (
           if c(a) then
             Bind(b(a), (a': A) => ProbWhileCut(c, b, n-1, a'))
           else
             Return(a)
         )
  }

  // Definition 39 / True iff mu(iset s | ProbWhile(c, b, a)(s) terminates) == 1
  ghost predicate ProbWhileTerminates<A(!new)>(b: A -> Hurd<A>, c: A -> bool) {
    var P := (a: A) => 
      (s: RNG) => exists n :: !c(ProbWhileCut(c, b, n, a)(s).0);
    forall a :: ForAllStar(P(a))
  }

  // Theorem 38
  function ProbWhile<A>(c: A -> bool, b: A -> Hurd<A>, a: A): (f: Hurd<A>)
    requires ProbWhileTerminates(b, c)
  {
    assume {:axiom} false;
    if c(a) then
      Bind(b(a), (a': A) => ProbWhile(c, b, a'))
    else
      Return(a)
  }

  method ProbWhileImperative<A>(c: A -> bool, b: A -> Hurd<A>, a: A, s: RNG) returns (t: (A, RNG)) 
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

  method ProbWhileImperativeAlternative<A>(c: A -> bool, b: A -> Hurd<A>, a: A, s: RNG) returns (t: (A, RNG)) 
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

  ghost predicate ProbUntilTerminates<A(!new)>(b: Hurd<A>, c: A -> bool) {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    ProbWhileTerminates(b', c')
  }

  // Definition 44
  function ProbUntil<A>(b: Hurd<A>, c: A -> bool): (f: Hurd<A>)
    requires ProbUntilTerminates(b, c)
    ensures 
      var c' := (a: A) => !c(a);
      var b' := (a: A) => b;
      forall s :: f(s) == ProbWhile(c', b', b(s).0)(b(s).1)
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    Bind(b, (a: A) => ProbWhile(c', b', a))
  }

  method ProbUntilImperative<A>(b: Hurd<A>, c: A -> bool, s: RNG) returns (t: (A, RNG))
    requires ProbUntilTerminates(b, c)
    ensures t == ProbUntil(b, c)(s)
    decreases *
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    t := ProbWhileImperative(c', b', b(s).0, b(s).1);
  }

  function Helper<A(!new)>(b: A -> Hurd<A>, c: A -> bool, a: A): (RNG -> bool) {
    (s: RNG) =>
      !c(b(a)(s).0)
  }

  function Helper2<A(!new)>(b: Hurd<A>, c: A -> bool): (RNG -> bool) {
    (s: RNG) =>
      c(b(s).0)
  }

  function Helper3<A>(b: Hurd<A>, c: A -> bool): (RNG -> bool)
    requires ProbUntilTerminates(b, c)
  {
    (s: RNG) =>
      c(ProbUntil(b, c)(s).0)
  }

  ghost function ConstructEvents<A>(b: Hurd<A>, c: A -> bool, d: A -> bool): (x: (iset<RNG>, iset<RNG>, iset<RNG>))
    requires ProbUntilTerminates(b, c)
  {
    (iset s | d(ProbUntil(b, c)(s).0), iset s | d(b(s).0) && c(b(s).0), iset s | c(b(s).0))
  }

  /*******
   Lemmas  
  *******/

  lemma EnsureProbUntilTerminates<A(!new)>(b: Hurd<A>, c: A -> bool)
    requires IsIndepFn(b)
    requires ExistsStar((s: RNG) => c(b(s).0))
    ensures ProbUntilTerminates(b, c)
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    var p := (s: RNG) => c(b(s).0);
    assert ProbUntilTerminates(b, c) by {
      forall a: A ensures IsIndepFn(b'(a)) {
        assert b'(a) == b;
      }
      forall a: A ensures ExistsStar(Helper(b', c', a)) {
        assert ExistsStar(p);
        assert (iset s | p(s)) == (iset s | Helper(b', c', a)(s));
      }
      assert ProbWhileTerminates(b', c') by {
        EnsureProbWhileTerminates(b', c');
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureProbWhileTerminates<A(!new)>(b: A -> Hurd<A>, c: A -> bool)
    requires forall a :: IsIndepFn(b(a))
    requires forall a :: ExistsStar(Helper(b, c, a))
    ensures ProbWhileTerminates(b, c)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} ProbUntilProbabilityFraction<A>(b: Hurd<A>, c: A -> bool, d: A -> bool)
    requires IsIndepFn(b)
    requires ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures
      var x := ConstructEvents(b, c, d);
      && x.0 in event_space
      && x.1 in event_space
      && x.2 in event_space
      && mu(x.2) != 0.0
      && mu(x.0) == mu(x.1) / mu(x.2)

  // Equation (3.39)
  lemma {:axiom} ProbUntilAsBind<A(!new)>(b: Hurd<A>, c: A -> bool, s: RNG)
    requires IsIndepFn(b)
    requires ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures ProbUntil(b, c) == Bind(b, (x: A) => if c(x) then Return(x) else ProbUntil(b, c))

  // Equation (3.40)
  lemma EnsureProbUntilTerminatesAndForAll<A(!new)>(b: Hurd<A>, c: A -> bool)
    requires IsIndepFn(b)
    requires ExistsStar(Helper2(b, c))
    ensures ProbUntilTerminates(b, c)
    ensures ForAllStar(Helper3(b, c))
  {
    EnsureProbUntilTerminates(b, c);
    assume {:axiom} ForAllStar(Helper3(b, c));
  }
}