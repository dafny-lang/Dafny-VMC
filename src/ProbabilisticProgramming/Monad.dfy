/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Monad {
  import Helper
  import Quantifier
  import Rand
  import Measures

  export
  provides
    Helper,
    Quantifier,
    Rand,
    Measures,
    Hurd,
    Return,
    Bind,
    Coin,
    While,
    WhileUnroll,
    WhileUnroll',
    Run,
    LiftInEventSpaceToResultEventSpace,
    LiftRestInEventSpaceToResultEventSpace
  reveals
    Result,
    Result.Map,
    Result.Bind,
    Result.In,
    Result.Equals,
    Result.Satisfies,
    Result.RestIn,
    Result.RestSatisfies,
    Values,
    Rests,
    ResultEventSpace,
    boolResultEventSpace,
    natResultEventSpace,
    ResultsWithValueIn,
    ResultsWithRestIn,
    Composition,
    Map,
    Join,
    WhileCut,
    WhileCutTerminates,
    WhileCutTerminatesWithFuel,
    WhileTerminatesAlmostSurely,
    LeastFuel

  export MonadInternals
  extends Monad
  reveals
    Hurd,
    Return,
    Bind,
    Coin,
    While,
    Run


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
      case Result(value, rest) => Run(f(value))(rest)
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

  ghost function Values<A>(results: iset<Result<A>>): iset<A> {
    iset r <- results | r.Result? :: r.value
  }

  ghost function Rests<A>(results: iset<Result<A>>): iset<Rand.Bitstream> {
    iset r <- results | r.Result? :: r.rest
  }

  ghost function ResultEventSpace<A(!new)>(eventSpace: iset<iset<A>>): iset<iset<Result<A>>> {
    iset e: iset<Result<A>> | Values(e) in eventSpace && Rests(e) in Rand.eventSpace
  }

  ghost const boolResultEventSpace: iset<iset<Result<bool>>> := ResultEventSpace(Measures.boolEventSpace)

  ghost const natResultEventSpace: iset<iset<Result<nat>>> := ResultEventSpace(Measures.natEventSpace)

  ghost function ResultsWithValueIn<A(!new)>(values: iset<A>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.value in values
  }

  ghost function ResultsWithRestIn<A(!new)>(rests: iset<Rand.Bitstream>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.rest in rests
  }

  // Equation (3.4)
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): (m: Hurd<B>)
    ensures forall s: Rand.Bitstream :: Run(m)(s) == Run(f)(s).Bind(g)
  {
    (s: Rand.Bitstream) => f(s).Bind(g)
  }

  // Equation (2.42)
  function Coin(): Hurd<bool>
    ensures forall s: Rand.Bitstream :: Run(Coin())(s) == Result(Rand.Head(s), Rand.Tail(s))
  {
    s => Result(Rand.Head(s), Rand.Tail(s))
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): (m: Hurd<A>)
    ensures forall s: Rand.Bitstream :: Run(m)(s) == Result(a, s)
  {
    (s: Rand.Bitstream) => Result(a, s)
  }

  function Map<A,B>(m: Hurd<A>, f: A -> B): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    Bind(ff, f => f)
  }

  function Run<A>(m: Hurd<A>): Rand.Bitstream -> Result<A> {
    m
  }

  ghost predicate WhileCutTerminates<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream) {
    exists fuel: nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
  }

  ghost function WhileCutTerminatesWithFuel<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream): nat -> bool {
    (fuel: nat) => !Run(WhileCut(condition, body, init, fuel))(s).Satisfies(condition)
  }

  // Definition 37
  function WhileCut<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, fuel: nat): Hurd<A> {
    if fuel == 0 || !condition(init) then
      Return(init)
    else
      Bind(body(init), (init': A) => WhileCut(condition, body, init', fuel - 1))
  }

  // Definition of while loops.
  // This definition is opaque because the details are not very useful.
  // For proofs, use the lemma `WhileUnroll`.
  // Equation (3.25), but modified to use `Diverging` instead of HOL's `arb` in case of nontermination
  opaque ghost function While<A(!new)>(condition: A -> bool, body: A -> Hurd<A>): (loop: A -> Hurd<A>)
    ensures forall s: Rand.Bitstream, init: A :: !condition(init) ==> Run(loop(init))(s) == Run(Return(init))(s)
  {
    var f :=
      (init: A) =>
        (s: Rand.Bitstream) =>
          if WhileCutTerminates(condition, body, init, s)
          then
            var fuel := LeastFuel(condition, body, init, s);
            WhileCut(condition, body, init, fuel)(s)
          else
            Diverging;
    assert forall s: Rand.Bitstream, init: A :: !condition(init) ==> f(init)(s) == Return(init)(s) by {
      forall s: Rand.Bitstream, init: A ensures !condition(init) ==> f(init)(s) == Return(init)(s) {
        if !condition(init) {
          assert WhileCutTerminatesWithFuel(condition, body, init, s)(0);
        }
      }
    }
    f
  }

  // Definition 39 / True iff Prob(iset s | While(condition, body, a)(s) terminates) == 1
  ghost predicate WhileTerminatesAlmostSurely<A(!new)>(condition: A -> bool, body: A -> Hurd<A>) {
    var p := (init: A) =>
               (s: Rand.Bitstream) => WhileCutTerminates(condition, body, init, s);
    forall init :: Quantifier.AlmostSurely(p(init))
  }

  ghost function LeastFuel<A>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream): (fuel: nat)
    requires WhileCutTerminates(condition, body, init, s)
    ensures WhileCutTerminatesWithFuel(condition, body, init, s)(fuel)
    ensures forall fuel': nat :: WhileCutTerminatesWithFuel(condition, body, init, s)(fuel') ==> fuel <= fuel'
  {
    var fuelBound :| WhileCutTerminatesWithFuel(condition, body, init, s)(fuelBound);
    Helper.Least(WhileCutTerminatesWithFuel(condition, body, init, s), fuelBound)
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
    assert Measures.IsSigmaAlgebra(Rand.eventSpace) by {
      Rand.ProbIsProbabilityMeasure();
    }
    assert Values(results) == event by {
      forall v: A ensures v in event <==> v in Values(results) {
        var s: Rand.Bitstream :| true;
        assert v in event <==> Result(v, s) in results;
      }
    }
    assert Rests(results) in Rand.eventSpace by {
      if v :| v in event {
        assert Rests(results) == Measures.SampleSpace() by {
          forall s: Rand.Bitstream ensures s in Rests(results) <==> s in Measures.SampleSpace() {
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
    requires Measures.SampleSpace() in eventSpace
    ensures ResultsWithRestIn(rests) in ResultEventSpace(eventSpace)
  {
    var results := ResultsWithRestIn(rests);
    assert Measures.IsSigmaAlgebra(Rand.eventSpace) by {
      Rand.ProbIsProbabilityMeasure();
    }
    assert Values(results) in eventSpace by {
      if rest :| rest in rests {
        assert Values(results) == Measures.SampleSpace() by {
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
    requires loop == While(condition, body)(init)(s)
    requires unrolled == While(condition, body)(init')(s')
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

  lemma WhileUnrollIfTerminates<A(!new)>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, fuel: nat, loop: Result<A>, unrolled: Result<A>)
    requires WhileCutTerminates(condition, body, init, s)
    requires fuel == LeastFuel(condition, body, init, s)
    requires loop == While(condition, body)(init)(s)
    requires unrolled == (if condition(init) then Bind(body(init), While(condition, body)) else Return(init))(s)
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
          While(condition, body)(init')(s');
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
    requires loop == While(condition, body)(init)(s)
    requires unrolled == (if condition(init) then Bind(body(init), While(condition, body)) else Return(init))(s)
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
  lemma WhileUnroll<A(!new)>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream)
    requires WhileTerminatesAlmostSurely(condition, body)
    ensures Run(While(condition, body)(init))(s) == Run(if condition(init) then Bind(body(init), While(condition, body)) else Return(init))(s)
  {
    var loop := While(condition, body)(init)(s);
    var unrolled := (if condition(init) then Bind(body(init), While(condition, body)) else Return(init))(s);
    assert loop == unrolled by {
      if WhileCutTerminates(condition, body, init, s) {
        var fuel: nat := LeastFuel(condition, body, init, s);
        WhileUnrollIfTerminates(condition, body, init, s, fuel, loop, unrolled);
      } else {
        WhileUnrollIfDiverges(condition, body, init, s, loop, unrolled);
      }
    }
  }

  lemma WhileUnroll'<A(!new)>(condition: A -> bool, body: A -> Hurd<A>, init: A, s: Rand.Bitstream, w: A -> Hurd<A>, i: Hurd<A>)
    requires WhileTerminatesAlmostSurely(condition, body)
    requires w == While(condition, body)
    requires i == if condition(init) then Bind(body(init), While(condition, body)) else Return(init)
    ensures Run(w(init))(s) == Run(i)(s)
  {
    WhileUnroll(condition, body, init, s);
  }
}

