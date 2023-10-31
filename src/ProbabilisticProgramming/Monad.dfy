/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Monad {
  import Rand
  import Measures
  import Quantifier

  export Spec provides
      Hurd,
      Return,
      Bind,
      Map,
      Until

  export reveals *

  /************
   Definitions
  ************/

  // The type (monad) of probabilistic computations (cf. Joe Hurd's PhD thesis).
  // For a given stream of bits (coin flips), it yields the result of the computation.
  type Hurd<A> = Rand.Bitstream -> Result<A>


  // The result of a probabilistic computation on a bitstream.
  // It either consists of the computed value and the (unconsumed) rest of the bitstream or indicates nontermination.
  // It differs from Hurd's definition in that the result can be nontermination, which Hurd does not model explicitly.
  datatype Result<A> =
    | Result(value: A, rest: Rand.Bitstream)
    | Diverging
  {
    function Map<B>(f: A -> B): Result<B> {
      match this
      case Diverging => Diverging
      case Result(value, rest) => Result(f(value), rest)
    }

    function Bind<B>(f: A -> Hurd<B>): Result<B> {
      match this
      case Diverging => Diverging
      case Result(value, rest) => f(value)(rest)
    }

    ghost predicate In(s: iset<A>) {
      Satisfies(x => x in s)
    }

    ghost predicate Equals(a: A) {
      Satisfies(x => x == a)
    }

    predicate Satisfies(property: A -> bool) {
      match this
      case Diverging => false
      case Result(value, _) => property(value)
    }

    ghost predicate RestIn(s: iset<Rand.Bitstream>) {
      RestSatisfies(r => r in s)
    }

    predicate RestSatisfies(property: Rand.Bitstream -> bool) {
      match this
      case Diverging => false
      case Result(_, rest) => property(rest)
    }
  }

  ghost function ResultSampleSpace<A(!new)>(sampleSpace: iset<A>): iset<Result<A>> {
    iset r: Result<A> | r.Diverging? || (r.value in sampleSpace && r.rest in Rand.sampleSpace)
  }

  ghost function Values<A>(results: iset<Result<A>>): iset<A> {
    iset r <- results | r.Result? :: r.value
  }

  ghost function Rests<A>(results: iset<Result<A>>): iset<Rand.Bitstream> {
    iset r <- results | r.Result? :: r.rest
  }

  ghost function ResultEventSpace<A(!new)>(eventSpace: iset<iset<A>>): iset<iset<Result<A>>> {
    iset e: iset<Result<A>> | Values(e) in eventSpace && Rests(e) in Rand.eventSpace
  }

  ghost const boolResultSampleSpace: iset<Result<bool>> := ResultSampleSpace(Measures.boolSampleSpace)

  ghost const boolResultEventSpace: iset<iset<Result<bool>>> := ResultEventSpace(Measures.boolEventSpace)

  ghost const natResultSampleSpace: iset<Result<nat>> := ResultSampleSpace(Measures.natSampleSpace)

  ghost const natResultEventSpace: iset<iset<Result<nat>>> := ResultEventSpace(Measures.natEventSpace)

  ghost function ResultsWithValueIn<A(!new)>(values: iset<A>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.value in values
  }

  ghost function ResultsWithRestIn<A(!new)>(rests: iset<Rand.Bitstream>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.rest in rests
  }

  // Equation (3.4)
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: Rand.Bitstream) => f(s).Bind(g)
  }

  // Equation (2.42)
  const Coin: Hurd<bool> := s => Result(Rand.Head(s), Rand.Tail(s))

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): Hurd<A> {
    (s: Rand.Bitstream) => Result(a, s)
  }

  function Map<A,B>(m: Hurd<A>, f: A -> B): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (s: Rand.Bitstream) => ff(s).Bind(f => f)
  }

  /*******
   Lemmas
  *******/

  lemma UnitalityBindReturn<A,B>(a: A, g: A -> Hurd<B>, s: Rand.Bitstream)
    ensures Bind(Return(a), g)(s) == g(a)(s)
  {}

  lemma BindIsAssociative<A,B,C>(f: Hurd<A>, g: A -> Hurd<B>, h: B -> Hurd<C>, s: Rand.Bitstream)
    ensures Bind(Bind(f, g), h)(s) == Bind(f, (a: A) => Bind(g(a), h))(s)
  {}

  lemma CompositionIsAssociative<A,B,C,D>(f: A -> Hurd<B>, g: B -> Hurd<C>, h: C -> Hurd<D>, a: A, s: Rand.Bitstream)
    ensures Composition(Composition(f, g), h)(a)(s) == Composition(f, Composition(g, h))(a)(s)
  {}

  lemma UnitalityJoinReturn<A>(f: Hurd<A>, s: Rand.Bitstream)
    ensures Join(Map(f, Return))(s) == Join(Return(f))(s)
  {}

  lemma JoinIsAssociative<A>(fff: Hurd<Hurd<Hurd<A>>>, s: Rand.Bitstream)
    ensures Join(Map(fff, Join))(s) == Join(Join(fff))(s)
  {}

  lemma LiftInEventSpaceToResultEventSpace<A(!new)>(event: iset<A>, eventSpace: iset<iset<A>>)
    requires event in eventSpace
    ensures ResultsWithValueIn(event) in ResultEventSpace(eventSpace)
  {
    var results := ResultsWithValueIn(event);
    assert Measures.IsSigmaAlgebra(Rand.eventSpace, Rand.sampleSpace) by {
      Rand.ProbIsProbabilityMeasure();
    }
    assert Rand.sampleSpace in Rand.eventSpace by {
      Measures.SampleSpaceInEventSpace(Rand.sampleSpace, Rand.eventSpace);
    }
    assert Values(results) == event by {
      forall v: A ensures v in event <==> v in Values(results) {
        var s: Rand.Bitstream :| true;
        assert v in event <==> Result(v, s) in results;
      }
    }
    assert Rests(results) in Rand.eventSpace by {
      if v :| v in event {
        assert Rests(results) == Rand.sampleSpace by {
          forall s: Rand.Bitstream ensures s in Rests(results) <==> s in Rand.sampleSpace {
            calc {
              s in Rests(results);
              Result(v, s) in results;
              true;
            }
          }
        }
      } else {
        assert Rests(results) == iset{};
      }
    }
  }

  lemma LiftRestInEventSpaceToResultEventSpace<A(!new)>(rests: iset<Rand.Bitstream>, eventSpace: iset<iset<A>>)
    requires rests in Rand.eventSpace
    requires iset{} in eventSpace
    requires Measures.Powerset<A>() in eventSpace
    ensures ResultsWithRestIn(rests) in ResultEventSpace(eventSpace)
  {
    var results := ResultsWithRestIn(rests);
    assert Measures.IsSigmaAlgebra(Rand.eventSpace, Rand.sampleSpace) by {
      Rand.ProbIsProbabilityMeasure();
    }
    assert Rand.sampleSpace in Rand.eventSpace by {
      Measures.SampleSpaceInEventSpace(Rand.sampleSpace, Rand.eventSpace);
    }
    assert Values(results) in eventSpace by {
      if rest :| rest in rests {
        assert Values(results) == Measures.Powerset<A>() by {
          forall v: A ensures v in Values(results) {
            assert Result(v, rest) in results;
          }
        }
      } else {
        assert Values(results) == iset{};
      }
    }
    assert Rests(results) in Rand.eventSpace by {
      if v: A :| true {
        assert Rests(results) == rests by {
          forall s: Rand.Bitstream ensures s in rests <==> s in Rests(results) {
            assert s in rests <==> Result(v, s) in results;
          }
        }
      } else {
        assert Rests(results) == iset{};
      }
    }
  }


  // INDEPENDENCE

  /************
  Definitions
  ************/

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Hurd<A>, A: iset<A>, E: iset<Rand.Bitstream>) {
    var e1 := iset s | f(s).RestIn(E);
    var e2 := iset s | f(s).In(A);
    Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
  }

  // Definition 33: (weak) independence
  ghost predicate IsIndepFunction<A(!new)>(f: Hurd<A>) {
    forall A: iset<A>, E: iset<Rand.Bitstream> | E in Rand.eventSpace :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35: (strong) independence
  ghost predicate {:axiom} IsIndep<A(!new)>(f: Hurd<A>)

  /*******
  Lemmas
  *******/

  lemma {:axiom} IsIndepImpliesMeasurableBool(f: Hurd<bool>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, boolResultEventSpace, f)

  lemma {:axiom} IsIndepImpliesMeasurableNat(f: Hurd<nat>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, natResultEventSpace, f)

  // Equation (3.14)
  lemma {:axiom} IsIndepImpliesIsIndepFunction<A(!new)>(f: Hurd<A>)
    requires IsIndep(f)
    ensures IsIndepFunction(f)

  // Equation (3.17)
  lemma {:axiom} CoinIsIndep()
    ensures IsIndep(Coin)

  // Equation (3.18)
  lemma {:axiom} ReturnIsIndep<T>(x: T)
    ensures IsIndep(Return(x))

  // Equation (3.19)
  lemma {:axiom} BindIsIndep<A, B>(f: Hurd<A>, g: A -> Hurd<B>)
    requires IsIndep(f)
    requires forall a :: IsIndep(g(a))
    ensures IsIndep(Bind(f, g))

  lemma AreIndepEventsConjunctElimination(e1: iset<Rand.Bitstream>, e2: iset<Rand.Bitstream>)
    requires Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
    ensures Rand.prob(e1 * e2) == Rand.prob(e1) * Rand.prob(e2)
  {}




  // LOOPS

  /************
   Definitions
  ************/

  // Definition 37
  function WhileCut<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, fuel: nat): Hurd<A> {
    if fuel == 0 || !condition(init) then
      Return(init)
    else
      Bind(body(init), (init': A) => WhileCut(condition, body, init', fuel - 1))
  }

  ghost predicate WhileCutTerminates<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream) {
    exists fuel: nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
  }

  ghost function WhileCutTerminatesWithFuel<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream): nat -> bool {
    (fuel: nat) => !WhileCut(condition, body, init, fuel)(s).Satisfies(condition)
  }

  // Definition 39 / True iff Prob(iset s | While(condition, body, a)(s) terminates) == 1
  ghost predicate WhileTerminatesAlmostSurely<A(!new)>(condition: A -> bool, body: A -> Hurd<A>) {
    var p := (init: A) =>
               (s: Rand.Bitstream) => WhileCutTerminates(condition, body, init, s);
    forall init :: Quantifier.AlmostSurely(p(init))
  }

  // Definition of while loops.
  // This definition is opaque because the details are not very useful.
  // For proofs, use the lemma `WhileUnroll`.
  // Equation (3.25), but modified to use `Monad.Diverging` instead of HOL's `arb` in case of nontermination
  // TODO: While(condition, body)(init) would be cleaner
  opaque ghost function While<A>(condition: A -> bool, body: A -> Hurd<A>, init: A): (f: Hurd<A>)
    ensures forall s: Rand.Bitstream :: !condition(init) ==> f(s) == Return(init)(s)
  {
    var f :=
      (s: Rand.Bitstream) =>
        if WhileCutTerminates(condition, body, init, s)
        then
          var fuel := LeastFuel(condition, body, init, s);
          WhileCut(condition, body, init, fuel)(s)
        else
          Diverging;
    assert forall s: Rand.Bitstream :: !condition(init) ==> f(s) == Return(init)(s) by {
      forall s: Rand.Bitstream ensures !condition(init) ==> f(s) == Return(init)(s) {
        if !condition(init) {
          assert WhileCutTerminatesWithFuel(condition, body, init, s)(0);
        }
      }
    }
    f
  }

  ghost function LeastFuel<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream): (fuel: nat)
    requires WhileCutTerminates(condition, body, init, s)
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

  ghost predicate UntilTerminatesAlmostSurely<A(!new)>(proposal: Hurd<A>, accept: A -> bool) {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    WhileTerminatesAlmostSurely(reject, body)
  }

  // Definition of until loops (rejection sampling).
  // For proofs, use the lemma `UntilUnroll`.
  // Definition 44
  ghost function Until<A>(proposal: Hurd<A>, accept: A -> bool): (f: Hurd<A>)
    //requires UntilTerminatesAlmostSurely(proposal, accept)
    // ensures
    //   var reject := (a: A) => !accept(a);
    //   var body := (a: A) => proposal;
    //   forall s :: f(s) == proposal(s).Bind(init => While(reject, body, init))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    Bind(proposal, (a: A) => While(reject, body, a))
  }

  function WhileLoopExitsAfterOneIteration<A(!new)>(body: A -> Hurd<A>, condition: A -> bool, init: A): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      body(init)(s).Satisfies(v => !condition(v))
  }

  function ProposalIsAccepted<A(!new)>(proposal: Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool) {
    (s: Rand.Bitstream) =>
      proposal(s).Satisfies(accept)
  }

  ghost function UntilLoopResultIsAccepted<A>(proposal: Hurd<A>, accept: A -> bool): (Rand.Bitstream -> bool)
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    (s: Rand.Bitstream) => Until(proposal, accept)(s).Satisfies(accept)
  }

  ghost function UntilLoopResultHasProperty<A>(proposal: Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
    requires UntilTerminatesAlmostSurely(proposal, accept)
  {
    iset s | Until(proposal, accept)(s).Satisfies(property)
  }

  ghost function ProposalIsAcceptedAndHasProperty<A>(proposal: Hurd<A>, accept: A -> bool, property: A -> bool): iset<Rand.Bitstream>
  {
    iset s | proposal(s).Satisfies(property) && proposal(s).Satisfies(accept)
  }

  ghost function ProposalAcceptedEvent<A>(proposal: Hurd<A>, accept: A -> bool): iset<Rand.Bitstream>
  {
    iset s | proposal(s).Satisfies(accept)
  }


  /*******
   Lemmas
  *******/

  lemma LeastFuelUnroll<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel': nat)
    requires WhileCutTerminates(condition, body, init', s')
    requires LeastFuel(condition, body, init', s') == fuel'
    requires condition(init)
    requires body(init)(s) == Result(init', s')
    ensures WhileCutTerminates(condition, body, init, s)
    ensures LeastFuel(condition, body, init, s) == fuel' + 1
  {
    assert WhileCutTerminates(condition, body, init, s) by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
    }
    var fuel := LeastFuel(condition, body, init, s);
    assert fuel == fuel' + 1 by {
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel');
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel - 1);
    }
  }

  lemma WhileCutUnroll<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == Result(init', s')
    ensures WhileCut(condition, body, init, fuel + 1)(s) == WhileCut(condition, body, init', fuel)(s')
  {}


  lemma WhileCutTerminatesWithFuelUnroll<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, fuel: nat)
    requires condition(init)
    requires body(init)(s) == Result(init', s')
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel + 1) == WhileCutTerminatesWithFuel(condition, body, init', s')(fuel)
  {}

  lemma WhileCutTerminatesUnroll<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream)
    requires condition(init)
    requires body(init)(s) == Result(init', s')
    ensures WhileCutTerminates(condition, body, init, s) == WhileCutTerminates(condition, body, init', s')
  {
    if WhileCutTerminates(condition, body, init, s) {
      var fuel: nat :| WhileCutTerminatesWithFuel(condition, body, init, s)(fuel);
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel - 1);
    }
    if WhileCutTerminates(condition, body, init', s') {
      var fuel: nat :| WhileCutTerminatesWithFuel(condition, body, init', s')(fuel);
      WhileCutTerminatesWithFuelUnroll(condition, body, init, s, init', s', fuel);
    }
  }

  lemma WhileUnrollIfConditionSatisfied<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, init': A, s': Rand.Bitstream, loop: Result<A>, unrolled: Result<A>)
    requires WhileCutTerminates(condition, body, init, s)
    requires condition(init)
    requires body(init)(s) == Result(init', s')
    requires loop == While(condition, body, init)(s)
    requires unrolled == While(condition, body, init')(s')
    ensures loop == unrolled
  {
    var fuel: nat := LeastFuel(condition, body, init, s);
    assert fuel >= 1;
    var fuel': nat := fuel - 1;
    assert WhileCutTerminatesWithFuel(condition, body, init', s')(fuel');
    assert WhileCutTerminates(condition, body, init', s');
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

  lemma WhileUnrollIfTerminates<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, fuel: nat, loop: Result<A>, unrolled: Result<A>)
    requires WhileCutTerminates(condition, body, init, s)
    requires fuel == LeastFuel(condition, body, init, s)
    requires loop == While(condition, body, init)(s)
    requires unrolled == (if condition(init) then Bind(body(init), (init': A) => While(condition, body, init')) else Return(init))(s)
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
          Diverging;
          unrolled;
        }
      case Result(init', s') =>
        calc {
          loop;
          { WhileUnrollIfConditionSatisfied(condition, body, init, s, init', s', loop, unrolled); }
          While(condition, body, init')(s');
          unrolled;
        }
    } else {
      calc {
        loop;
        Result(init, s);
        unrolled;
      }
    }
  }

  lemma WhileUnrollIfDiverges<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, loop: Result<A>, unrolled: Result<A>)
    requires !WhileCutTerminates(condition, body, init, s)
    requires loop == While(condition, body, init)(s)
    requires unrolled == (if condition(init) then Bind(body(init), (init': A) => While(condition, body, init')) else Return(init))(s)
    ensures loop == unrolled == Diverging
  {
    reveal While();
    match body(init)(s)
    case Diverging =>
      assert unrolled == Diverging;
    case Result(init', s') =>
      assert !WhileCutTerminates(condition, body, init', s') by {
        WhileCutTerminatesUnroll(condition, body, init, s, init', s');
      }
  }

  // Theorem 38
  lemma WhileUnroll<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream)
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures While(condition, body, init)(s) == (if condition(init) then Bind(body(init), (init': A) => While(condition, body, init')) else Return(init))(s)
  {
    var loop := While(condition, body, init)(s);
    var unrolled := (if condition(init) then Bind(body(init), (init': A) => While(condition, body, init')) else Return(init))(s);
    assert loop == unrolled by {
      if WhileCutTerminates(condition, body, init, s) {
        var fuel: nat := LeastFuel(condition, body, init, s);
        WhileUnrollIfTerminates(condition, body, init, s, fuel, loop, unrolled);
      } else {
        WhileUnrollIfDiverges(condition, body, init, s, loop, unrolled);
      }
    }
  }

  lemma EnsureUntilTerminates<A(!new)>(proposal: Hurd<A>, accept: A -> bool)
    requires IsIndep(proposal)
    requires Quantifier.WithPosProb((s: Rand.Bitstream) => proposal(s).Satisfies(accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var proposalIsAccepted := (s: Rand.Bitstream) => proposal(s).Satisfies(accept);
    assert UntilTerminatesAlmostSurely(proposal, accept) by {
      forall a: A ensures IsIndep(body(a)) {
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
  lemma {:axiom} EnsureWhileTerminates<A(!new)>(condition: A -> bool, body: A -> Hurd<A>)
    requires forall a :: IsIndep(body(a))
    requires forall a :: Quantifier.WithPosProb(WhileLoopExitsAfterOneIteration(body, condition, a))
    ensures WhileTerminatesAlmostSurely(condition, body)

  // Theorem 45 (wrong!) / PROB_BERN_UNTIL (correct!)
  lemma {:axiom} UntilProbabilityFraction<A>(proposal: Hurd<A>, accept: A -> bool, d: A -> bool)
    requires IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
    ensures
      && UntilLoopResultHasProperty(proposal, accept, d) in Rand.eventSpace
      && ProposalIsAcceptedAndHasProperty(proposal, accept, d) in Rand.eventSpace
      && ProposalAcceptedEvent(proposal, accept) in Rand.eventSpace
      && Rand.prob(ProposalAcceptedEvent(proposal, accept)) != 0.0
      && Rand.prob(UntilLoopResultHasProperty(proposal, accept, d)) == Rand.prob(ProposalIsAcceptedAndHasProperty(proposal, accept, d)) / Rand.prob(ProposalAcceptedEvent(proposal, accept))

  // Equation (3.39)
  lemma UntilUnroll<A(!new)>(proposal: Hurd<A>, accept: A -> bool, s: Rand.Bitstream)
    requires IsIndep(proposal)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures Until(proposal, accept)(s) == Bind(proposal, (x: A) => if accept(x) then Return(x) else Until(proposal, accept))(s)
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    match proposal(s)
    case Diverging =>
    case Result(init, s') => WhileUnroll(reject, body, init, s');
  }

  // Equation (3.40)
  lemma EnsureUntilTerminatesAndForAll<A(!new)>(proposal: Hurd<A>, accept: A -> bool)
    requires IsIndep(proposal)
    requires Quantifier.WithPosProb(ProposalIsAccepted(proposal, accept))
    ensures UntilTerminatesAlmostSurely(proposal, accept)
    ensures Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept))
  {
    EnsureUntilTerminates(proposal, accept);
    assume {:axiom} Quantifier.AlmostSurely(UntilLoopResultIsAccepted(proposal, accept)); // add later
  }

  lemma WhileCutIsIndep<A(!new)>(condition: A -> bool, body: A -> Hurd<A>, init: A, fuel: nat)
    requires forall a: A :: IsIndep(body(a))
    ensures IsIndep(WhileCut(condition, body, init, fuel))
  {
    if fuel == 0 || !condition(init) {
      ReturnIsIndep(init);
    } else {
      forall init': A ensures IsIndep(WhileCut(condition, body, init', fuel - 1)) {
        WhileCutIsIndep(condition, body, init', fuel - 1);
      }
      BindIsIndep(body(init), init' => WhileCut(condition, body, init', fuel - 1));
    }
  }

  lemma WhileIsIndep<A(!new)>(condition: A -> bool, body: A -> Hurd<A>, init: A)
    requires forall a: A :: IsIndep(body(a))
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures IsIndep(While(condition, body, init))
  {
    // To prove this, we need a definition of Independence.IsIndep
    assume {:axiom} false;
  }

  lemma UntilIsIndep<A(!new)>(proposal: Hurd<A>, accept: A -> bool)
    requires IsIndep(proposal)
    requires UntilTerminatesAlmostSurely(proposal, accept)
    ensures IsIndep(Until(proposal, accept))
  {
    var reject := (a: A) => !accept(a);
    var body := (a: A) => proposal;
    var f := (init: A) => While(reject, body, init);
    forall init: A ensures IsIndep(f(init)) {
      WhileIsIndep(reject, body, init);
    }
    BindIsIndep(proposal, f);
  }

}

