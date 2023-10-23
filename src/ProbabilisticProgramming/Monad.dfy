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
}

