/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Loops {
  import Helper
  import Measures
  import Limits
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

  ghost predicate WhileTerminatesOn<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream) {
    exists fuel: nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
  }

  ghost function WhileCutTerminatesWithFuel<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream): nat -> bool {
    (fuel: nat) => !WhileCut(condition, body, init, fuel)(s).Satisfies(condition)
  }

  ghost function WhileCutDivergenceProbability<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): nat -> real {
    (fuel: nat) => Rand.prob(iset s | !WhileCutTerminatesWithFuel(condition, body, init, s)(fuel))
  }

  ghost predicate WhileTerminatesAlmostSurelyInit<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A) {
    Quantifier.AlmostSurely((s: Rand.Bitstream) => WhileTerminatesOn(condition, body, init, s))
  }

  // Definition 39 / True iff Prob(iset s | While(condition, body)(a)(s) terminates) == 1
  ghost predicate WhileTerminatesAlmostSurely<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>) {
    forall init :: WhileTerminatesAlmostSurelyInit(condition, body, init)
  }

  // Definition of while loops.
  // This definition is opaque because the details are not very useful.
  // For proofs, use the lemma `WhileUnroll`.
  // Equation (3.25), but modified to use `Monad.Diverging` instead of HOL's `arb` in case of nontermination
  opaque ghost function While<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>): (loop: A -> Monad.Hurd<A>) {
    var f :=
      (init: A) =>
        (s: Rand.Bitstream) =>
          if WhileTerminatesOn(condition, body, init, s)
          then
            var fuel := LeastFuel(condition, body, init, s);
            WhileCut(condition, body, init, fuel)(s)
          else
            Monad.Diverging;
    assert forall s: Rand.Bitstream, init: A :: !condition(init) ==> f(init)(s) == Monad.Return(init)(s) by {
      forall s: Rand.Bitstream, init: A ensures !condition(init) ==> f(init)(s) == Monad.Return(init)(s) {
        if !condition(init) {
          assert WhileCutTerminatesWithFuel(condition, body, init, s)(0);
        }
      }
    }
    f
  }

  ghost function LeastFuel<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream): (fuel: nat)
    requires WhileTerminatesOn(condition, body, init, s)
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
    ensures forall fuel': nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel') ==> fuel <= fuel'
  {
    var fuelBound :| WhileCutTerminatesWithFuel(condition, body, init, s)(fuelBound);
    Least(WhileCutTerminatesWithFuel(condition, body, init, s), fuelBound)
  }

  ghost function Least(property: nat -> bool, bound: nat, start: nat := 0): (l: nat)
    decreases bound - start
    requires start <= bound
    requires property(bound)
    ensures property(l)
    ensures start <= l <= bound
    ensures forall n: nat | start <= n :: property(n) ==> l <= n
  {
    if start == bound || property(start)
    then start
    else Least(property, bound, start + 1)
  }

  ghost predicate UntilTerminatesAlmostSurely<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    WhileTerminatesAlmostSurely(reject, body)
  }

  // Definition of until loops (rejection sampling).
  // For proofs, use the lemma `UntilUnroll`.
  // Definition 44
  ghost function Until<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (f: Monad.Hurd<A>)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures
      var reject := (a: A) => !accept(a);
      var body := (a: A) => proposal;
      forall s :: f(s) == proposal(s).Bind(While(reject, body))
    ensures
      forall s | f(s).Result? :: accept(f(s).value)
  {
    reveal While();
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Monad.Bind(proposal, While(reject, body))
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      body(init)(s).Satisfies(v => !condition(v))
  }

  ghost function WhileLoopGloballyExitsAfterOneIteration<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>): Rand.Bitstream -> bool {
    (s: Rand.Bitstream) => forall init: A :: WhileLoopExitsAfterOneIteration(condition, body, init)(s)
  }

  function ProposalIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      proposal(s).Satisfies(accept)
  }

  ghost function UntilLoopResultIsAccepted<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool)
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    (s: Rand.Bitstream) => Until(proposal, accept)(s).Satisfies(accept)
  }

  ghost function UntilLoopResultHasProperty<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    iset s | Until(proposal, accept)(s).Satisfies(property)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Monad.Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
  {
    iset s | proposal(s).Satisfies(property) && proposal(s).Satisfies(accept)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Monad.Hurd<A>, accept: A -> bool): iset<Rand.Bitstream>
  {
    iset s | proposal(s).Satisfies(accept)
  }


  /*******
   Lemmas
  *******/

  lemma LeastFuelUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel': nat)
    requires WhileTerminatesOn(condition, body, init', s')
    requires LeastFuel(condition, body, init', s') == fuel'
    requires condition(init)
    requires body(init)(s) == Monad.Result(init', s')
    ensures WhileTerminatesOn(condition, body, init, s)
    ensures LeastFuel(condition, body, init, s) == fuel' + 1
  {
    assert WhileTerminatesOn(condition, body, init, s) by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
    }
    var fuel := LeastFuel(condition, body, init, s);
    assert fuel == fuel' + 1 by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel - 1);
    }
  }

  lemma WhileCutUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == Monad.Result(init', s')
    ensures WhileCut(condition, body, init, fuel + 1)(s) == WhileCut(condition, body, init', fuel)(s')
  {}


  lemma WhileCutTerminatesWithFuelUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == Monad.Result(init', s')
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel + 1) == WhileCutTerminatesWithFuel(condition, body, init', s')(fuel)
  {}

  lemma WhileCutTerminatesUnroll<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream)
    requires condition(init)
    requires body(init)(s) == Monad.Result(init', s')
    ensures WhileTerminatesOn(condition, body, init, s) == WhileTerminatesOn(condition, body, init', s')
  {
    if WhileTerminatesOn(condition, body, init, s) {
      var fuel: nat :| WhileCutTerminatesWithFuel(condition, body, init, s)(fuel);
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel - 1);
    }
    if WhileTerminatesOn(condition, body, init', s') {
      var fuel: nat :| WhileCutTerminatesWithFuel(condition, body, init', s')(fuel);
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel);
    }
  }

  lemma WhileUnrollIfConditionSatisfied<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, loop: Monad.Result<A>, unrolled: Monad.Result<A>)
    requires WhileTerminatesOn(condition, body, init, s)
    requires condition(init)
    requires body(init)(s) == Monad.Result(init', s')
    requires loop == While(condition, body)(init)(s)
    requires unrolled == While(condition, body)(init')(s')
    ensures loop == unrolled
  {
    var fuel: nat := LeastFuel(condition, body, init, s);
    assert fuel >= 1;
    var fuel': nat := fuel - 1;
    assert WhileCutTerminatesWithFuel(condition, body, init', s')(fuel');
    assert WhileTerminatesOn(condition, body, init', s');
    var minFuel: nat := LeastFuel(condition, body, init', s');
    assert minFuel == fuel' by {
      LeastFuelUnroll(condition, body, init, s, init', s', minFuel);
    }
    assert loop == unrolled by {
      calc {
        loop;
        { reveal While(); }
        WhileCut(condition, body, init, fuel)(s);
        { WhileCutUnroll(condition, body, init, s, init', s', fuel'); }
        WhileCut(condition, body, init', fuel')(s');
        { reveal While(); }
        unrolled;
      }
    }
  }

  lemma WhileUnrollIfTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, fuel: nat, loop: Monad.Result<A>, unrolled: Monad.Result<A>)
    requires WhileTerminatesOn(condition, body, init, s)
    requires fuel == LeastFuel(condition, body, init, s)
    requires loop == While(condition, body)(init)(s)
    requires unrolled == (if condition(init) then Monad.Bind(body(init), While(condition, body)) else Monad.Return(init))(s)
    ensures loop == unrolled
  {
    if condition(init) {
      assert fuel >= 1;
      match body(init)(s)
      case Diverging =>
        calc {
          loop;
          { reveal While(); }
          WhileCut(condition, body, init, fuel)(s);
          Monad.Diverging;
          unrolled;
        }
      case Result(init', s') =>
        calc {
          loop;
          { WhileUnrollIfConditionSatisfied(condition, body, init, s, init', s', loop, unrolled); }
          While(condition, body)(init')(s');
          unrolled;
        }
    } else {
      WhileInitialConditionNegated(condition, body, init, s);
      calc {
        loop;
        Monad.Result(init, s);
        unrolled;
      }
    }
  }

  lemma WhileUnrollIfDiverges<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream, loop: Monad.Result<A>, unrolled: Monad.Result<A>)
    requires !WhileTerminatesOn(condition, body, init, s)
    requires loop == While(condition, body)(init)(s)
    requires unrolled == (if condition(init) then Monad.Bind(body(init), While(condition, body)) else Monad.Return(init))(s)
    ensures loop == unrolled == Monad.Diverging
  {
    reveal While();
    if !condition(init) {
      WhileInitialConditionNegated(condition, body, init, s);
    }
    match body(init)(s)
    case Diverging =>
      assert unrolled == Monad.Diverging;
    case Result(init', s') =>
      assert !WhileTerminatesOn(condition, body, init', s') by {
        WhileCutTerminatesUnroll(condition, body, init, s, init', s');
      }
  }

  // Theorem 38
  lemma WhileUnroll<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream)
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures While(condition, body)(init)(s) == (if condition(init) then Monad.Bind(body(init), While(condition, body)) else Monad.Return(init))(s)
  {
    var loop := While(condition, body)(init)(s);
    var unrolled := (if condition(init) then Monad.Bind(body(init), While(condition, body)) else Monad.Return(init))(s);
    assert loop == unrolled by {
      if WhileTerminatesOn(condition, body, init, s) {
        var fuel: nat := LeastFuel(condition, body, init, s);
        WhileUnrollIfTerminates(condition, body, init, s, fuel, loop, unrolled);
      } else {
        WhileUnrollIfDiverges(condition, body, init, s, loop, unrolled);
      }
    }
  }

  lemma EnsureUntilTerminates<A(!new)>(proposal: Monad.Hurd<A>, accept: A -> bool)
    requires Independence.IsIndep(proposal)
    requires Quantifier.WithPosProb((s: Rand.Bitstream) => proposal(s).Satisfies(accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: Rand.Bitstream) => proposal(s).Satisfies(accept);
    assert UntilTerminatesAlmostSurely(proposal, accept) by {
      forall a: A ensures Independence.IsIndep(body(a)) {
        assert body(a) == proposal;
      }
      forall a: A ensures Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(reject, body, a)) {
        assert Quantifier.WithPosProb(proposalIsAccepted);
        assert (iset s | proposalIsAccepted(s)) == (iset s | WhileLoopExitsAfterOneIteration(reject, body, a)(s));
      }
      assert WhileTerminatesAlmostSurely(reject, body) by {
        assert Quantifier.WithPosProb(WhileLoopGloballyExitsAfterOneIteration(reject, body)) by {
          var acceptsImmediately := (s: Rand.Bitstream) => proposal(s).Satisfies(accept);
          var event1 := iset s | acceptsImmediately(s);
          var event2 := iset s | WhileLoopGloballyExitsAfterOneIteration(reject, body)(s);
          assert event1 <= event2 by {
            forall s ensures s in event1 ==> s in event2 {
              assert acceptsImmediately(s) ==> WhileLoopGloballyExitsAfterOneIteration(reject, body)(s) by {
                if acceptsImmediately(s) {
                  forall a: A ensures WhileLoopExitsAfterOneIteration(reject, body, a)(s) {
                    assert proposal == body(a);
                  }
                }
              }
            }
          }
          assert event2 in Rand.eventSpace by {
            if inhabitant: A :| true {
              assert event2 <= event1 by {
                forall s ensures s in event2 ==> s in event1 {
                  assert proposal == body(inhabitant);
                  if s in event2 {
                    calc {
                      WhileLoopGloballyExitsAfterOneIteration(reject, body)(s);
                      WhileLoopExitsAfterOneIteration(reject, body, inhabitant)(s);
                      acceptsImmediately(s);
                    }
                  }
                }
              }
              assert event1 == event2;
            } else {
              assert event2 == iset s :: s by {
                forall s ensures s in event2 {
                  forall a: A ensures WhileLoopExitsAfterOneIteration(reject, body, a)(s) {
                    assert false;
                  }
                }
              }
            }
          }
          calc ==> {
            Quantifier.WithPosProb(acceptsImmediately);
            Rand.prob(event1) > 0.0;
            { Rand.ProbIsProbabilityMeasure(); Measures.IsMonotonic(Rand.eventSpace, Rand.prob, event1, event2); }
            Rand.prob(event2) > 0.0;
            Quantifier.WithPosProb(WhileLoopGloballyExitsAfterOneIteration(reject, body));
          }
        }
        EnsureWhileTerminates(reject, body);
      }
    }
  }

  // (Equation 3.30) / Sufficient conditions for while-loop termination
  lemma {:axiom} EnsureWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>)
    requires forall a :: Independence.IsIndep(body(a))
    requires Quantifier.WithPosProb(WhileLoopGloballyExitsAfterOneIteration(condition, body))
    ensures WhileTerminatesAlmostSurely(condition, body)

  lemma {:axiom} EnsureWhileTerminatesAlmostSurelyViaLimit<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A)
    requires Limits.ConvergesTo(WhileCutDivergenceProbability(condition, body, init), 0.0)
    ensures WhileTerminatesAlmostSurelyInit(condition, body, init)
  /*
    Proof strategy:

    Prove that the event that WhileCut terminates grows with the fuel.
    By monotonicity of probability, the probability is increasing with the fuel.
    The event that while terminates is the union of WhileCut terminating over all possible values for fuel.
    By standard measure theory results and the monotonicity of the events,
    the probability that while terminates is the supremum of the probabilities that WhileCut terminates over all possible values for fuel.
    Since the probability is increasing, the supremum is the same as the limit.
  */

  ghost function WhileCutProbability<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, resultSet: iset<A>): nat -> real {
    (fuel: nat) => Rand.prob(Monad.BitstreamsWithValueIn(WhileCut(condition, body, init, fuel), resultSet))
  }

  lemma {:axiom} WhileProbabilityViaLimit<A(!new)>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, resultSet: iset<A>, resultSetRestricted: iset<A>, limit: real)
    // TODO: we should probably require measurability of condition and independence of body(a) for all a?
    requires resultSetRestricted == iset a <- resultSet | !condition(a)
    requires Limits.ConvergesTo(WhileCutProbability(condition, body, init, resultSetRestricted), limit)
    ensures Rand.prob(Monad.BitstreamsWithValueIn(While(condition, body)(init), resultSet)) == limit
  /*
    Proof strategy (similar to EnsureWhileTerminates, can they be unified?):

    Prove that the event that WhileCut yields a result in resultSet violating `condition` grows with the fuel.
    By monotonicity of probability, the probability is increasing with the fuel.
    The event that while yields a result in resultsSet (it always violates `condition`) is the union of the events of WhileCut yielding a value in `resultSetRestricted`, over all possible values for fuel.
    By standard measure theory results and the monotonicity of the events,
    the probability that while yields a result in resultSet is the supremum of the probabilities that WhileCut yields a result in resultSet violating `condition`, over all possible values for fuel.
    Since the probability is increasing, the supremum is the same as the limit.
  */

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
    match proposal(s)
    case Diverging =>
    case Result(init, s') => WhileUnroll(reject, body, init, s');
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
    ensures Independence.IsIndep(While(condition, body)(init))
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
    forall init: A ensures Independence.IsIndep(While(reject, body)(init)) {
      WhileIsIndep(reject, body, init);
    }
    Independence.BindIsIndep(proposal, While(reject, body));
  }

  lemma WhileNegatesCondition<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream)
    requires While(condition, body)(init)(s).Result?
    ensures !condition(While(condition, body)(init)(s).value)
  {
    reveal While();
  }

  lemma WhileInitialConditionNegated<A>(condition: A -> bool, body: A -> Monad.Hurd<A>, init: A, s: Rand.Bitstream)
    ensures !condition(init) ==> While(condition, body)(init)(s) == Monad.Return(init)(s)
  {
    reveal While();
  }
}
