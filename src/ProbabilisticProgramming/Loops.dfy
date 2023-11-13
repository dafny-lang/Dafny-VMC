/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Loops {
  import Monad
  import Quantifier
  import Independence
  import Rand

  /************
   Definitions
  ************/

  ghost predicate UntilTerminatesAlmostSurely<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.WhileTerminatesAlmostSurely(reject, body)
  }

  // Definition of until loops (rejection sampling).
  // For proofs, use the lemma `UntilUnroll`.
  // Definition 44
  ghost function Until<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures
      var reject := (a: A) => !accept(a);
      var body := (a: A) => proposal;
      forall s :: Monad.Run(f)(s) == Monad.Run(proposal)(s).Bind(Monad.While(reject, body))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, Monad.While(reject, body))
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Monad.Hurd<A>, condition: A -> bool, init: A): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      Monad.Run(body(init))(s).Satisfies(v => !condition(v))
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      Monad.Run(proposal)(s).Satisfies(accept)
  }

  ghost function UntilLoopResultIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool)
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    (s: Rand.Bitstream) => Monad.Run(Until(proposal, accept))(s).Satisfies(accept)
  }

  ghost function UntilLoopResultHasProperty<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    iset s | Monad.Run(Until(proposal, accept))(s).Satisfies(property)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
  {
    iset s | Monad.Run(proposal)(s).Satisfies(property) && Monad.Run(proposal)(s).Satisfies(accept)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<Rand.Bitstream>
  {
    iset s | Monad.Run(proposal)(s).Satisfies(accept)
  }


  /*******
   Lemmas
  *******/

  lemma EnsureUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb((s: Rand.Bitstream) => Monad.Run(proposal)(s).Satisfies(accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: Rand.Bitstream) => Monad.Run(proposal)(s).Satisfies(accept);
    assert UntilTerminatesAlmostSurely(proposal, accept) by {
      forall a: A ensures Independence.IsIndep(body(a)) {
        assert body(a) == proposal;
      }
      forall a: A ensures Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, reject, a)) {
        assert Quantifier.WithPosProb(proposalIsAccepted);
        assert (iset s | proposalIsAccepted(s)) == (iset s | WhileLoopExitsAfterOneIteration(body, reject, a)(s));
      }
      assert Monad.WhileTerminatesAlmostSurely(reject, body) by {
        EnsureWhileTerminates(reject, body);
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>)
    requires forall a :: Independence.IsIndep(body(a))
    requires forall a :: Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, condition, a))
    ensures Monad.WhileTerminatesAlmostSurely(condition, body)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} UntilProbabilityFraction<A>(proposal: Monad.Hurd<A>, accept: A -> bool, d: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
    ensures
      && UntilLoopResultHasProperty(proposal, accept, d) in Rand.eventSpace
      && ProposalIsAcceptedAndHasProperty(proposal, accept, d) in Rand.eventSpace
      && ProposalAcceptedEvent(proposal, accept) in Rand.eventSpace
      && Rand.prob(ProposalAcceptedEvent(proposal, accept)) != 0.0
      && Rand.prob(UntilLoopResultHasProperty(proposal, accept, d)) == Rand.prob(ProposalIsAcceptedAndHasProperty(proposal, accept, d)) / Rand.prob(ProposalAcceptedEvent(proposal, accept))

  // Equation (3.39)
  lemma UntilUnroll<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, s: Rand.Bitstream)
    requires Independence.IsIndep(proposal)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures Monad.Run(Until(proposal, accept))(s) == Monad.Run(Monad.Bind(proposal, (x: A) => if accept(x) then Monad.Return(x) else Until(proposal, accept)))(s)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    match Monad.Run(proposal)(s)
    case Diverging =>
    case Result(init, s') => {
      assert Monad.Run(Monad.While(reject, body)(init))(s') == Monad.Run(if reject(init) then Monad.Bind(body(init), Monad.While(reject, body)) else Monad.Return(init))(s') by {
        Monad.WhileUnroll(reject, body, init, s');
      }
    }
  }

  // Equation (3.40)
  lemma EnsureUntilTerminatesAndForAll<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
    ensures Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept))
  {
    EnsureUntilTerminates(proposal, accept);
    assume {:axiom} Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept)); // add later
  }

  lemma WhileCutIsIndep<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, fuel: nat)
    requires forall a: A :: Independence.IsIndep(body(a))
    ensures Independence.IsIndep(Monad.WhileCut(condition, body, init, fuel))
  {
    if fuel == 0 || !condition(init) {
      Independence.ReturnIsIndep(init);
    } else {
      forall init': A ensures Independence.IsIndep(Monad.WhileCut(condition, body, init', fuel - 1)) {
        WhileCutIsIndep(condition, body, init', fuel - 1);
      }
      Independence.BindIsIndep(body(init), init' => Monad.WhileCut(condition, body, init', fuel - 1));
    }
  }

  lemma WhileIsIndep<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires forall a: A :: Independence.IsIndep(body(a))
    requires Monad.WhileTerminatesAlmostSurely(condition, body)
    ensures Independence.IsIndep(Monad.While(condition, body)(init))
  {
    // To prove this, we need a definition of Independence.IsIndep
    assume {:axiom} false;
  }

  lemma UntilIsIndep<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures Independence.IsIndep(Until(proposal, accept))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    forall init: A ensures Independence.IsIndep(Monad.While(reject, body)(init)) {
      WhileIsIndep(reject, body, init);
    }
    Independence.BindIsIndep(proposal, Monad.While(reject, body));
  }
}
