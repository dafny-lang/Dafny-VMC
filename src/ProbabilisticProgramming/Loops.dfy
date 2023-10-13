/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Loops {
  import Monad
  import Quantifier
  import Independence
  import Random

  /************
   Definitions
  ************/

  // Definition 37
  function WhileCut<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, n: nat, init: A): Monad.Hurd<A> {
    if n == 0 then
      Monad.Return(init)
    else (
           if condition(init) then
             Monad.Bind(body(init), (a: A) => WhileCut(condition, body, n-1, a))
           else
             Monad.Return(init)
         )
  }

  // Definition 39 / True iff Prob(iset s | While(condition, body, a)(s) terminates) == 1
  ghost predicate WhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>) {
    var p := (a: A) =>
               (s: Random.Bitstream) => exists n :: !condition(WhileCut(condition, body, n, a)(s).0);
    forall a :: Quantifier.AlmostSurely(p(a))
  }

  // Theorem 38
  function While<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): (f: Monad.Hurd<A>)
    requires WhileTerminates(condition, body)
  {
    assume {:axiom} false; // assume termination
    if condition(init) then
      Monad.Bind(body(init), (a': A) => While(condition, body, a'))
    else
      Monad.Return(init)
  }

  method WhileImperative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Random.Bitstream) returns (t: (A, Random.Bitstream))
    requires WhileTerminates(condition, body)
    ensures While(condition, body, init)(s) == t
    decreases *
  {
    while condition(init)
      decreases *
    {
      var (a, s) := body(init)(s);
    }
    return (init, s);
  }

  method WhileImperativeAlternative<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Random.Bitstream) returns (t: (A, Random.Bitstream))
    requires WhileTerminates(condition, body)
    ensures While(condition, body, init)(s) == t
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

  ghost predicate UntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    WhileTerminates(reject, body)
  }

  // Definition 44
  function Until<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
    requires UntilTerminates(proposal, accept)
    ensures
      var reject := (a: A) => !accept(a);
      var body := (a: A) => proposal;
      forall s :: f(s) == While(reject, body, proposal(s).0)(proposal(s).1)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, (a: A) => While(reject, body, a))
  }

  method UntilImperative<A>(proposal: Monad.Hurd<A>, accept: A -> bool, s: Random.Bitstream) returns (t: (A, Random.Bitstream))
    requires UntilTerminates(proposal, accept)
    ensures t == Until(proposal, accept)(s)
    decreases *
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    t := WhileImperative(reject, body, proposal(s).0, proposal(s).1);
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Monad.Hurd<A>, condition: A -> bool, init: A): (Random.Bitstream -> bool) {
    (s: Random.Bitstream) =>
      !condition(body(init)(s).0)
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Random.Bitstream -> bool) {
    (s: Random.Bitstream) =>
      accept(proposal(s).0)
  }

  function UntilLoopResultIsAccepted<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (Random.Bitstream -> bool)
    requires UntilTerminates(proposal, accept)
  {
    (s: Random.Bitstream) =>
      accept(Until(proposal, accept)(s).0)
  }

  ghost function UntilLoopResultHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Random.Bitstream>
    requires UntilTerminates(proposal, accept)
  {
    iset s | property(Until(proposal, accept)(s).0)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Random.Bitstream>
  {
    iset s | property(proposal(s).0) && accept(proposal(s).0)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<Random.Bitstream>
  {
    iset s | accept(proposal(s).0)
  }


  /*******
   Lemmas
  *******/

  lemma EnsureUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb((s: Random.Bitstream) => accept(proposal(s).0))
    ensures UntilTerminates(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: Random.Bitstream) => accept(proposal(s).0);
    assert UntilTerminates(proposal, accept) by {
      forall a: A ensures Independence.IsIndep(body(a)) {
        assert body(a) == proposal;
      }
      forall a: A ensures Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, reject, a)) {
        assert Quantifier.WithPosProb(proposalIsAccepted);
        assert (iset s | proposalIsAccepted(s)) == (iset s | WhileLoopExitsAfterOneIteration(body, reject, a)(s));
      }
      assert WhileTerminates(reject, body) by {
        EnsureWhileTerminates(reject, body);
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>)
    requires forall a :: Independence.IsIndep(body(a))
    requires forall a :: Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, condition, a))
    ensures WhileTerminates(condition, body)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} UntilProbabilityFraction<A>(proposal: Monad.Hurd<A>, accept: A -> bool, d: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminates(proposal, accept)
    ensures
      && UntilLoopResultHasProperty(proposal, accept, d) in Random.eventSpace
      && ProposalIsAcceptedAndHasProperty(proposal, accept, d) in Random.eventSpace
      && ProposalAcceptedEvent(proposal, accept) in Random.eventSpace
      && Random.Prob(ProposalAcceptedEvent(proposal, accept)) != 0.0
      && Random.Prob(UntilLoopResultHasProperty(proposal, accept, d)) == Random.Prob(ProposalIsAcceptedAndHasProperty(proposal, accept, d)) / Random.Prob(ProposalAcceptedEvent(proposal, accept))

  // Equation (3.39)
  lemma {:axiom} UntilAsBind<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, s: Random.Bitstream)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminates(proposal, accept)
    ensures Until(proposal, accept) == Monad.Bind(proposal, (x: A) => if accept(x) then Monad.Return(x) else Until(proposal, accept))

  // Equation (3.40)
  lemma EnsureUntilTerminatesAndForAll<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminates(proposal, accept)
    ensures Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept))
  {
    EnsureUntilTerminates(proposal, accept);
    assume {:axiom} Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept)); // add later
  }

  lemma WhileIsIndep<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires forall a: A :: Independence.IsIndep(body(a))
    requires WhileTerminates(condition, body)
    ensures Independence.IsIndep(While(condition, body, init))
  {
    if condition(init) {
      forall a ensures Independence.IsIndep(While(condition, body, a)) {
        assume {:axiom} false; // circular reasoning, rewrite this proof
        WhileIsIndep(condition, body, a);
      }
      Independence.IndepFnIsCompositional(body(init), a => While(condition, body, a));
    } else {
      Independence.ReturnIsIndep(init);
    }
  }

  lemma UntilIsIndep<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires UntilTerminates(proposal, accept)
    ensures Independence.IsIndep(Until(proposal, accept))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    forall init: A {
      WhileIsIndep(reject, body, init);
    }
    Independence.IndepFnIsCompositional(proposal, (init: A) => While(reject, body, init));
  }
}
