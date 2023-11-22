/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Monad {
  import Rand
  import Measures

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

    predicate IsFailure() {
      Diverging?
    }

    function PropagateFailure(): Result<A>
      requires Diverging?
    {
      Diverging
    }

    function Extract(): (A, Rand.Bitstream)
      requires Result?
    {
      (this.value, this.rest)
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

  ghost function BitstreamsWithValueIn<A(!new)>(h: Hurd<A>, aSet: iset<A>): iset<Rand.Bitstream> {
    iset s | h(s).In(aSet)
  }

  ghost function BitstreamsWithRestIn<A(!new)>(h: Hurd<A>, restSet: iset<Rand.Bitstream>): iset<Rand.Bitstream> {
    iset s | h(s).RestIn(restSet)
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
}

