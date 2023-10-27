/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Monad {
  import Rand
  import Measures

  export Spec 
  provides 
    Hurd, 
    Return,
    Bind,
    Coin, 
    Eval, 
    Rand,
    Map,
    Result, 
    Result.RestIn, 
    Result.In, 
    Result.Satisfies,
    Result.Bind,
    Result.Map,
    Result.Equals,
    Result.IsConverging,
    Result.IsDiverging,
    Result.ValueOf,
    Result.RestOf,
    DivergingResult,
    ConvergingResult,
    ResultsWithValueIn,
    ResultsWithRestIn,
    ResultEventSpace,
    LiftInEventSpaceToResultEventSpace,
    LiftRestInEventSpaceToResultEventSpace,
    boolResultEventSpace,
    natResultEventSpace,
    Measures
  reveals
    IsAlwaysConverging

  export extends Spec

  export Loops extends Spec reveals Hurd, Result, Result.Bind, Result.Satisfies, Return, Bind

  export UniformPowerOfTwo extends Spec reveals Hurd, Result, Bind, Result.Bind, Eval

  export Uniform extends Spec reveals Hurd, Result

  export Bernoulli extends Spec reveals Hurd, Result

  export BernoulliExpNeg extends Spec reveals Hurd, Result

  export Independence extends Spec reveals Hurd


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

    function Bind<B>(f: A -> Hurd<B>): (r: Result<B>) 
      ensures this.IsConverging() && IsAlwaysConverging(f(this.ValueOf())) ==> r.IsConverging()
    {
      match this
      case Diverging => Diverging
      case Result(value, rest) => Eval(f(value), rest)
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

    predicate IsConverging() {
      Result?
    }

    predicate IsDiverging() {
      Diverging?
    }

    function ValueOf(): A
      requires this.IsConverging()
    {
      this.value
    }

    function RestOf(): Rand.Bitstream
      requires this.IsConverging()
    {
      this.rest
    }
  }

  function ConvergingResult<A>(value: A, rest: Rand.Bitstream): Result<A> {
    Result(value, rest)
  }

  function DivergingResult<A>(): Result<A> {
    Diverging
  }

  ghost predicate IsAlwaysConverging<A>(f: Hurd<A>) {
    forall s :: Eval(f, s).IsConverging()
  }

  ghost function ResultSampleSpace<A(!new)>(sampleSpace: iset<A>): iset<Result<A>> {
    iset r: Result<A> | r.IsDiverging() || (r.value in sampleSpace && r.rest in Rand.sampleSpace)
  }

  ghost function Values<A>(results: iset<Result<A>>): iset<A> {
    iset r <- results | r.IsConverging():: r.ValueOf()
  }

  ghost function Rests<A>(results: iset<Result<A>>): iset<Rand.Bitstream> {
    iset r <- results | r.IsConverging() :: r.RestOf()
  }

  ghost function ResultEventSpace<A(!new)>(eventSpace: iset<iset<A>>): iset<iset<Result<A>>> {
    iset e: iset<Result<A>> | Values(e) in eventSpace && Rests(e) in Rand.eventSpace
  }

  ghost const boolResultSampleSpace: iset<Result<bool>> := ResultSampleSpace(Measures.boolSampleSpace)

  ghost const boolResultEventSpace: iset<iset<Result<bool>>> := ResultEventSpace(Measures.boolEventSpace)

  ghost const natResultSampleSpace: iset<Result<nat>> := ResultSampleSpace(Measures.natSampleSpace)

  ghost const natResultEventSpace: iset<iset<Result<nat>>> := ResultEventSpace(Measures.natEventSpace)

  ghost function ResultsWithValueIn<A(!new)>(values: iset<A>): iset<Result<A>> {
    iset result: Result<A> | result.IsConverging() && result.ValueOf() in values
  }

  ghost function ResultsWithRestIn<A(!new)>(rests: iset<Rand.Bitstream>): iset<Result<A>> {
    iset result: Result<A> | result.IsConverging() && result.RestOf() in rests
  }

  // Equation (3.4)
  function Bind<A(!new),B>(f: Hurd<A>, g: A -> Hurd<B>): (h: Hurd<B>)
    ensures IsAlwaysConverging(f) && (forall a :: IsAlwaysConverging(g(a))) ==> IsAlwaysConverging(h)
  {
    (s: Rand.Bitstream) => Eval(f, s).Bind(g)
  }

  // Equation (2.42)
  function Coin(): (f: Hurd<bool>) 
    ensures IsAlwaysConverging(f)
  {
    s => Result(Rand.Head(s), Rand.Tail(s))
  }

  function Composition<A,B(!new),C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): (h: Hurd<A>)
    ensures IsAlwaysConverging(h)
  {
    (s: Rand.Bitstream) => Result(a, s)
  }

  function Map<A(!new),B>(m: Hurd<A>, f: A -> B): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (s: Rand.Bitstream) => ff(s).Bind(f => f)
  }

  function Eval<A>(f: Hurd<A>, s: Rand.Bitstream): Result<A> {
    f(s)
  }

  // A tail recursive version of Sample, closer to the imperative implementation
  function UniformPowerOfTwoTailRecursive(n: nat, u: nat := 0): Hurd<nat>
    requires n >= 1
  {
    (s: Rand.Bitstream) =>
      if n == 1 then
        Result(u, s)
      else
        UniformPowerOfTwoTailRecursive(n / 2, if Rand.Head(s) then 2*u + 1 else 2*u)(Rand.Tail(s))
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

/*   lemma IsAlwaysConvergingPointwise<A>(h: Hurd<A>)
    requires IsAlwaysConverging(h)
    ensures forall s :: Eval(h, s).IsConverging()
  {
    forall s ensures Eval(h, s).IsConverging() {
      assert IsAlwaysConverging(h);
    }
  } */
  
}

