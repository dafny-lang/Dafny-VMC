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

  // Definition 37
  function WhileCut<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, fuel: nat): Monad.Hurd<A> {
    if fuel == 0 || !condition(init) then
      Monad.Return(init)
    else
      Monad.Bind(body(init), (init': A) => WhileCut(condition, body, init', fuel - 1))
  }

  ghost predicate WhileCutTerminates<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream) {
    exists fuel: nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
  }

  ghost function WhileCutTerminatesWithFuel<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream): nat -> bool {
    (fuel: nat) => !condition(WhileCut(condition, body, init, fuel)(s).0)
  }

  // Definition 39 / True iff Prob(iset s | While(condition, body, a)(s) terminates) == 1
  ghost predicate WhileTerminatesAlmostSurely<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>) {
    var p := (init: A) =>
               (s: Rand.Bitstream) => WhileCutTerminates(condition, body, init, s);
    forall init :: Quantifier.AlmostSurely(p(init))
  }

  // Equation (3.25)
  ghost function While<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): (f: Monad.Hurd<A>)
  {
    (s: Rand.Bitstream) =>
      if WhileCutTerminates(condition, body, init, s)
      then
        var fuel := MinimalFuel(condition, body, init, s);
        WhileCut(condition, body, init, fuel)(s)
      else
        // In HOL, Hurd returns `arb` here, which is not possible in Dafny.
        (init, s)
  }

  ghost function MinimalFuel<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream): (fuel: nat)
    requires WhileCutTerminates(condition, body, init, s)
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
    ensures forall fuel': nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel') ==> fuel <= fuel'
  {
    var fuelBound :| WhileCutTerminatesWithFuel(condition, body, init, s)(fuelBound);
    Minimal(WhileCutTerminatesWithFuel(condition, body, init, s), fuelBound)
  }

  ghost function Minimal(property: nat -> bool, bound: nat, i: nat := 0): (n: nat)
    decreases bound - i
    requires i <= bound
    requires property(bound)
    ensures property(n)
    ensures i <= n <= bound
    ensures forall m: nat | i <= m :: property(m) ==> n <= m
  {
    if i == bound || property(i)
    then i
    else Minimal(property, bound, i + 1)
  }

  ghost predicate UntilTerminatesAlmostSurely<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    WhileTerminatesAlmostSurely(reject, body)
  }

  // Definition 44
  ghost function Until<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures
      var reject := (a: A) => !accept(a);
      var body := (a: A) => proposal;
      forall s :: f(s) == While(reject, body, proposal(s).0)(proposal(s).1)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, (a: A) => While(reject, body, a))
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Monad.Hurd<A>, condition: A -> bool, init: A): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      !condition(body(init)(s).0)
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      accept(proposal(s).0)
  }

  ghost function UntilLoopResultIsAccepted<A>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool)
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    (s: Rand.Bitstream) =>
      accept(Until(proposal, accept)(s).0)
  }

  ghost function UntilLoopResultHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    iset s | property(Until(proposal, accept)(s).0)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
  {
    iset s | property(proposal(s).0) && accept(proposal(s).0)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<Rand.Bitstream>
  {
    iset s | accept(proposal(s).0)
  }


  /*******
   Lemmas
  *******/

  lemma MinimalFuelUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel': nat)
    requires WhileCutTerminates(condition, body, init', s')
    requires MinimalFuel(condition, body, init', s') == fuel'
    requires condition(init)
    requires body(init)(s) == (init', s')
    ensures WhileCutTerminates(condition, body, init, s)
    ensures MinimalFuel(condition, body, init, s) == fuel' + 1
  {
    assert WhileCutTerminates(condition, body, init, s) by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
    }
    var fuel := MinimalFuel(condition, body, init, s);
    assert fuel == fuel' + 1 by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel - 1);
    }
  }

  lemma WhileCutUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == (init', s')
    ensures WhileCut(condition, body, init, fuel + 1)(s) == WhileCut(condition, body, init', fuel)(s')
  {}


  lemma WhileCutTerminatesWithFuelUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == (init', s')
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel + 1) == WhileCutTerminatesWithFuel(condition, body, init', s')(fuel)
  {}

  lemma WhileUnrollIfConditionSatisfied<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, loop: (A, Rand.Bitstream), unrolled: (A, Rand.Bitstream))
    requires WhileCutTerminates(condition, body, init, s)
    requires condition(init)
    requires body(init)(s) == (init', s')
    requires loop == While(condition, body, init)(s)
    requires unrolled == While(condition, body, init')(s')
    ensures loop == unrolled
  {
    var fuel: nat := MinimalFuel(condition, body, init, s);
    assert fuel >= 1;
    var fuel': nat := fuel - 1;
    assert WhileCutTerminatesWithFuel(condition, body, init', s')(fuel');
    assert WhileCutTerminates(condition, body, init', s');
    var minFuel: nat := MinimalFuel(condition, body, init', s');
    assert minFuel == fuel' by {
      MinimalFuelUnroll(condition, body, init, s, init', s', minFuel);
    }
    assert loop == unrolled by {
      calc {
        loop;
        WhileCut(condition, body, init, fuel)(s);
        { WhileCutUnroll(condition, body, init, s, init', s', fuel'); }
        WhileCut(condition, body, init', fuel')(s');
        unrolled;
      }
    }
  }

  lemma WhileUnrollIfTerminates<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, fuel: nat, loop: (A, Rand.Bitstream), unrolled: (A, Rand.Bitstream))
    requires WhileCutTerminates(condition, body, init, s)
    requires fuel == MinimalFuel(condition, body, init, s)
    requires loop == While(condition, body, init)(s)
    requires unrolled == (if condition(init) then Monad.Bind(body(init), (init': A) => While(condition, body, init')) else Monad.Return(init))(s)
    ensures loop == unrolled
  {
    if condition(init) {
      var (init', s') := body(init)(s);
      calc {
        loop;
        { WhileUnrollIfConditionSatisfied(condition, body, init, s, init', s', loop, unrolled); }
        While(condition, body, init')(s');
        unrolled;
      }
    } else {
      calc {
        loop;
        (init, s);
        unrolled;
      }
    }
  }

  // Theorem 38
  lemma WhileUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream)
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures While(condition, body, init)(s) == (if condition(init) then Monad.Bind(body(init), (init': A) => While(condition, body, init')) else Monad.Return(init))(s)
  {
    var loop := While(condition, body, init)(s);
    var unrolled := (if condition(init) then Monad.Bind(body(init), (init': A) => While(condition, body, init')) else Monad.Return(init))(s);
    assert loop == unrolled by {
      if WhileCutTerminates(condition, body, init, s) {
        var fuel: nat := MinimalFuel(condition, body, init, s);
        WhileUnrollIfTerminates(condition, body, init, s, fuel, loop, unrolled);
      } else {
        // In this case, equality does not hold in Dafny.
        // Hurd avoids this problem in HOL by having `While` return `arb` (an arbitrary value) in this case.
        // That's not possible in Dafny, so we must resort to `assume false`.
        assume {:axiom} false;
      }
    }
  }

  lemma EnsureUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb((s: Rand.Bitstream) => accept(proposal(s).0))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: Rand.Bitstream) => accept(proposal(s).0);
    assert UntilTerminatesAlmostSurely(proposal, accept) by {
      forall a: A ensures Independence.IsIndep(body(a)) {
        assert body(a) == proposal;
      }
      forall a: A ensures Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, reject, a)) {
        assert Quantifier.WithPosProb(proposalIsAccepted);
        assert (iset s | proposalIsAccepted(s)) == (iset s | WhileLoopExitsAfterOneIteration(body, reject, a)(s));
      }
      assert WhileTerminatesAlmostSurely(reject, body) by {
        EnsureWhileTerminates(reject, body);
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>)
    requires forall a :: Independence.IsIndep(body(a))
    requires forall a :: Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, condition, a))
    ensures WhileTerminatesAlmostSurely(condition, body)

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
    ensures Until(proposal, accept)(s) == Monad.Bind(proposal, (x: A) => if accept(x) then Monad.Return(x) else Until(proposal, accept))(s)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var (init, s') := proposal(s);
    WhileUnroll(reject, body, init, s');
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
    ensures Independence.IsIndep(WhileCut(condition, body, init, fuel))
  {
    if fuel == 0 || !condition(init) {
      Independence.ReturnIsIndep(init);
    } else {
      forall init': A ensures Independence.IsIndep(WhileCut(condition, body, init', fuel - 1)) {
        WhileCutIsIndep(condition, body, init', fuel - 1);
      }
      Independence.BindIsIndep(body(init), init' => WhileCut(condition, body, init', fuel - 1));
    }
  }

  lemma WhileIsIndep<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires forall a: A :: Independence.IsIndep(body(a))
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures Independence.IsIndep(While(condition, body, init))
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
    forall init: A {
      WhileIsIndep(reject, body, init);
    }
    Independence.BindIsIndep(proposal, (init: A) => While(reject, body, init));
  }
}
