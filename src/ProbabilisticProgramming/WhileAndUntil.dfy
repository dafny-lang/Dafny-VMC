/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module WhileAndUntil {
  import Partials
  import Monad
  import Quantifier
  import Independence
  import RandomNumberGenerator

  /************
   Definitions
  ************/

  // Definition 37
  function ProbWhileCut<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, fuel: nat, init: A): Monad.Hurd<A> {
    if fuel == 0 then
      Monad.Diverge()
    else (
           if condition(init) then
             Monad.Bind(body(init), (a: A) => ProbWhileCut(condition, body, fuel - 1, a))
           else
             Monad.Return(init)
         )
  }

  ghost predicate ProbWhileTerminatesOn<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: RandomNumberGenerator.RNG) {
    exists fuel: nat :: ProbWhileCut(condition, body, fuel, init)(s).Terminating?
  }

  // Definition 39 / True iff mu(iset s | ProbWhile(condition, body, a)(s) terminates) == 1
  ghost predicate ProbWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>) {
    forall init :: Quantifier.ForAllStar((s: RandomNumberGenerator.RNG) => ProbWhileTerminatesOn(condition, body, init, s))
  }

  // Theorem 38
  ghost function ProbWhile<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): (f: Monad.Hurd<A>)
  {
    (s: RandomNumberGenerator.RNG) =>
      if ProbWhileTerminatesOn(condition, body, init, s)
      then
        var fuel :| ProbWhileCut(condition, body, fuel, init)(s).Terminating?;
        ProbWhileCut(condition, body, fuel, init)(s)
      else
        Monad.Diverging
  }

  method ProbWhileImperative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: RandomNumberGenerator.RNG) returns (t: Monad.Result<A>)
    ensures ProbWhile(condition, body, init)(s) == t
    decreases *

  method ProbWhileImperativeAlternative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: RandomNumberGenerator.RNG) returns (t: Monad.Result<A>)
    ensures ProbWhile(condition, body, init)(s) == t
    decreases *

  ghost predicate ProbUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    ProbWhileTerminates(reject, body)
  }

  // Definition 44
  ghost function ProbUntil<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, (a: A) => ProbWhile(reject, body, a))
  }

  method ProbUntilImperative<A>(proposal: Monad.Hurd<A>, accept: A -> bool, s: RandomNumberGenerator.RNG) returns (t: Monad.Result<A>)
    ensures t == ProbUntil(proposal, accept)(s)
    decreases *
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    match proposal(s) {
      case Diverging => t := Monad.Diverging;
      case Terminating(init, s') => t := ProbWhileImperative(reject, body, init, s');
    }
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Monad.Hurd<A>, condition: A -> bool, init: A): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      !body(init)(s).ValueSatisfies(condition)
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (RandomNumberGenerator.RNG -> bool) {
    (s: RandomNumberGenerator.RNG) =>
      proposal(s).ValueSatisfies(accept)
  }

  ghost function UntilLoopResultIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (RandomNumberGenerator.RNG -> bool)
  {
    (s: RandomNumberGenerator.RNG) =>
      ProbUntil(proposal, accept)(s).ValueSatisfies(accept)
  }

  ghost function UntilLoopResultHasProperty<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<RandomNumberGenerator.RNG>
  {
    iset s | ProbUntil(proposal, accept)(s).ValueSatisfies(property)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<RandomNumberGenerator.RNG>
  {
    iset s |
      && proposal(s).ValueSatisfies(property)
      && proposal(s).ValueSatisfies(accept)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<RandomNumberGenerator.RNG>
  {
    iset s | proposal(s).ValueSatisfies(accept)
  }


  /*******
   Lemmas
  *******/

  lemma EnsureProbUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndepFn(proposal)
    requires Quantifier.ExistsStar((s: RandomNumberGenerator.RNG) => proposal(s).ValueSatisfies(accept))
    ensures ProbUntilTerminates(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: RandomNumberGenerator.RNG) => proposal(s).ValueSatisfies(accept);
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
    assume {:axiom} Quantifier.ForAllStar(UntilLoopResultIsAccepted(proposal, accept)); // add later
  }

  lemma ProbWhileIsIndepFn<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires forall a: A :: Independence.IsIndepFn(body(a))
    requires ProbWhileTerminates(condition, body)
    ensures Independence.IsIndepFn(ProbWhile(condition, body, init))
  {
    if condition(init) {
      forall a ensures Independence.IsIndepFn(ProbWhile(condition, body, a)) {
        assume {:axiom} false; // circular reasoning, rewrite this proof
        ProbWhileIsIndepFn(condition, body, a);
      }
      Independence.IndepFnIsCompositional(body(init), a => ProbWhile(condition, body, a));
    } else {
      Independence.PartialReturnIsIndepFn(init);
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
