/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module WhileAndUntil {
  import Monad
  import Quantifier
  import Independence
  import RandomNumberGenerator

  /************
   Definitions
  ************/

  // Definition 37
  function ProbWhileCut<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, n: nat, init: A): Monad.Hurd<A> {
    if n == 0 then
      Monad.Return(init)
    else (
           if condition(init) then
             Monad.Bind(body(init), (a: A) => ProbWhileCut(condition, body, n-1, a))
           else
             Monad.Return(init)
         )
  }

  // Definition 39 / True iff mu(iset s | ProbWhile(condition, body, a)(s) terminates) == 1
  ghost predicate ProbWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>) {
    var p := (a: A) =>
               (s: RandomNumberGenerator.RNG) => exists n :: !condition(ProbWhileCut(condition, body, n, a)(s).0);
    forall a :: Quantifier.ForAllStar(p(a))
  }

  // Theorem 38
  function ProbWhile<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): (f: Monad.Hurd<A>)
    requires ProbWhileTerminates(condition, body)
  {
    assume {:axiom} false;
    if condition(init) then
      Monad.Bind(body(init), (a': A) => ProbWhile(condition, body, a'))
    else
      Monad.Return(init)
  }

  method ProbWhileImperative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbWhileTerminates(condition, body)
    ensures ProbWhile(condition, body, init)(s) == t
    decreases *
  {
    while condition(init)
      decreases *
    {
      var (a, s) := body(init)(s);
    }
    return (init, s);
  }

  method ProbWhileImperativeAlternative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbWhileTerminates(condition, body)
    ensures ProbWhile(condition, body, init)(s) == t
    decreases *
  {
    while true
      decreases *
    {
      if !condition(init) {
        return (init, s);
      } else {
        var (a, s) := body(init)(s);
      }
    }
  }

  ghost predicate ProbUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    ProbWhileTerminates(reject, body)
  }

  // Definition 44
  function ProbUntil<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
    requires ProbUntilTerminates(proposal, accept)
    ensures
      var reject := (a: A) => !accept(a);
      var body := (a: A) => proposal;
      forall s :: f(s) == ProbWhile(reject, body, proposal(s).0)(proposal(s).1)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, (a: A) => ProbWhile(reject, body, a))
  }

  method ProbUntilImperative<A>(proposal: Monad.Hurd<A>, accept: A -> bool, s: RandomNumberGenerator.RNG) returns (t: (A, RandomNumberGenerator.RNG))
    requires ProbUntilTerminates(proposal, accept)
    ensures t == ProbUntil(proposal, accept)(s)
    decreases *
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    t := ProbWhileImperative(reject, body, proposal(s).0, proposal(s).1);
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Monad.Hurd<A>, condition: A -> bool, init: A): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      !condition(body(init)(s).0)
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      accept(proposal(s).0)
  }

  function UntilLoopResultIsAccepted<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (RandomNumberGenerator.RNG -> bool)
    requires ProbUntilTerminates(proposal, accept)
  {
    (s: RandomNumberGenerator.RNG) =>
      accept(ProbUntil(proposal, accept)(s).0)
  }

  ghost function UntilLoopResultHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<RandomNumberGenerator.RNG>
    requires ProbUntilTerminates(proposal, accept)
  {
    iset s | property(ProbUntil(proposal, accept)(s).0)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<RandomNumberGenerator.RNG>
  {
    iset s | property(proposal(s).0) && accept(proposal(s).0)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<RandomNumberGenerator.RNG>
  {
    iset s | accept(proposal(s).0)
  }


  /*******
   Lemmas
  *******/

  lemma EnsureProbUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndepFn(proposal)
    requires Quantifier.ExistsStar((s: RandomNumberGenerator.RNG) => accept(proposal(s).0))
    ensures ProbUntilTerminates(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: RandomNumberGenerator.RNG) => accept(proposal(s).0);
    assert ProbUntilTerminates(proposal, accept) by {
      forall a: A ensures Independence.IsIndepFn(body(a)) {
        assert body(a) == proposal;
      }
      forall a: A ensures Quantifier.ExistsStar(WhileLoopExitsAfterOneIteration(body, reject, a)) {
        assert Quantifier.ExistsStar(proposalIsAccepted);
        assert (iset s | proposalIsAccepted(s)) == (iset s | WhileLoopExitsAfterOneIteration(body, reject, a)(s));
      }
      assert ProbWhileTerminates(reject, body) by {
        EnsureProbWhileTerminates(reject, body);
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureProbWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>)
    requires forall a :: Independence.IsIndepFn(body(a))
    requires forall a :: Quantifier.ExistsStar(WhileLoopExitsAfterOneIteration(body, condition, a))
    ensures ProbWhileTerminates(condition, body)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} ProbUntilProbabilityFraction<A>(proposal: Monad.Hurd<A>, accept: A -> bool, d: A -> bool)
    requires Independence.IsIndepFn(proposal)
    requires Quantifier.ExistsStar(ProposalIsAccepted(proposal, accept))
    ensures ProbUntilTerminates(proposal, accept)
    ensures
      && UntilLoopResultHasProperty(proposal, accept, d) in RandomNumberGenerator.event_space
      && ProposalIsAcceptedAndHasProperty(proposal, accept, d) in RandomNumberGenerator.event_space
      && ProposalAcceptedEvent(proposal, accept) in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(ProposalAcceptedEvent(proposal, accept)) != 0.0
      && RandomNumberGenerator.mu(UntilLoopResultHasProperty(proposal, accept, d)) == RandomNumberGenerator.mu(ProposalIsAcceptedAndHasProperty(proposal, accept, d)) / RandomNumberGenerator.mu(ProposalAcceptedEvent(proposal, accept))

  // Equation (3.39)
  lemma {:axiom} ProbUntilAsBind<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, s: RandomNumberGenerator.RNG)
    requires Independence.IsIndepFn(proposal)
    requires Quantifier.ExistsStar(ProposalIsAccepted(proposal, accept))
    ensures ProbUntilTerminates(proposal, accept)
    ensures ProbUntil(proposal, accept) == Monad.Bind(proposal, (x: A) => if accept(x) then Monad.Return(x) else ProbUntil(proposal, accept))

  // Equation (3.40)
  lemma EnsureProbUntilTerminatesAndForAll<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndepFn(proposal)
    requires Quantifier.ExistsStar(ProposalIsAccepted(proposal, accept))
    ensures ProbUntilTerminates(proposal, accept)
    ensures Quantifier.ForAllStar(UntilLoopResultIsAccepted(proposal, accept))
  {
    EnsureProbUntilTerminates(proposal, accept);
    assume {:axiom} Quantifier.ForAllStar(UntilLoopResultIsAccepted(proposal, accept));
  }

  lemma ProbWhileIsIndepFn<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires forall a: A :: Independence.IsIndepFn(body(a))
    requires ProbWhileTerminates(condition, body)
    ensures Independence.IsIndepFn(ProbWhile(condition, body, init))
  {
    if condition(init) {
      forall a ensures Independence.IsIndepFn(ProbWhile(condition, body, a)) {
        assume {:axiom} false; // assume termination
        ProbWhileIsIndepFn(condition, body, a);
      }
      Independence.IndepFnIsCompositional(body(init), a => ProbWhile(condition, body, a));
    } else {
      Independence.ReturnIsIndepFn(init);
    }
  }

  lemma ProbUntilIsIndepFn<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndepFn(proposal)
    requires ProbUntilTerminates(proposal, accept)
    ensures Independence.IsIndepFn(ProbUntil(proposal, accept))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    forall init: A {
      ProbWhileIsIndepFn(reject, body, init);
    }
    Independence.IndepFnIsCompositional(proposal, (init: A) => ProbWhile(reject, body, init));
  }
}
