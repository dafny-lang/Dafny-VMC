/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Monad {
  import RandomNumberGenerator
  import MeasureTheory

  /************
   Definitions
  ************/

  type Hurd<A> = RandomNumberGenerator.RNG -> (A, RandomNumberGenerator.RNG)

  // Equation (2.38)
  function Tail(s: RandomNumberGenerator.RNG): (s': RandomNumberGenerator.RNG) {
    TailIsRNG(s);
    (n: nat) => s(n+1)
  }

  function IterateTail(s: RandomNumberGenerator.RNG, n: nat): (t: RandomNumberGenerator.RNG)
    ensures t(0) == s(n)
  {
    if n == 0 then
      s
    else
      IterateTail(Tail(s), n - 1)
  }

  lemma TailOfIterateTail(s: RandomNumberGenerator.RNG, n: nat)
    ensures Tail(IterateTail(s, n)) == IterateTail(s, n + 1)
  {}

  // Equation (2.37)
  function Head(s: RandomNumberGenerator.RNG): bool {
    s(0)
  }

  // Equation (2.42)
  function Deconstruct(s: RandomNumberGenerator.RNG): (bool, RandomNumberGenerator.RNG) {
    (Head(s), Tail(s))
  }

  // Equation (2.41)
  function Drop(n: nat, s: RandomNumberGenerator.RNG): (s': RandomNumberGenerator.RNG)
    ensures Head(s') == s(n)
  {
    if n == 0 then
      s
    else
      Drop(n - 1, Tail(s))
  }

  // Equation (3.4)
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: RandomNumberGenerator.RNG) =>
      var (a, s') := f(s);
      g(a)(s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): Hurd<A> {
    (s: RandomNumberGenerator.RNG) => (a, s)
  }

  function Map<A,B>(f: A -> B, m: Hurd<A>): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (s: RandomNumberGenerator.RNG) =>
      var (f, s') := ff(s);
      f(s')
  }

  /*******
   Lemmas
  *******/

  lemma UnitalityBindReturn<A,B>(a: A, g: A -> Hurd<B>, s: RandomNumberGenerator.RNG)
    ensures Bind(Return(a), g)(s) == g(a)(s)
  {}

  lemma BindIsAssociative<A,B,C>(f: Hurd<A>, g: A -> Hurd<B>, h: B -> Hurd<C>, s: RandomNumberGenerator.RNG)
    ensures Bind(Bind(f, g), h)(s) == Bind(f, (a: A) => Bind(g(a), h))(s)
  {
    var (a, s') := f(s);
    var (a', s'') := g(a)(s');
    assert (a', s'') == Bind(f, g)(s);
    calc {
      Bind(Bind(f, g), h)(s);
      h(a')(s'');
      Bind(g(a), h)(s');
      Bind(f, (a: A) => Bind(g(a), h))(s);
    }
  }

  lemma CompositionIsAssociative<A,B,C,D>(f: A -> Hurd<B>, g: B -> Hurd<C>, h: C -> Hurd<D>, a: A, s: RandomNumberGenerator.RNG)
    ensures Composition(Composition(f, g), h)(a)(s) == Composition(f, Composition(g, h))(a)(s)
  {
    BindIsAssociative(f(a), g, h, s);
  }

  lemma UnitalityJoinReturn<A>(f: Hurd<A>, s: RandomNumberGenerator.RNG)
    ensures Join(Map(Return, f))(s) == Join(Return(f))(s)
  {
    var (a, t) := f(s);
    calc {
      Join(Return(f))(s);
    ==
      (a, t);
    ==
      Join(Map(Return, f))(s);
    }
  }

  lemma JoinIsAssociative<A>(fff: Hurd<Hurd<Hurd<A>>>, s: RandomNumberGenerator.RNG)
    ensures Join(Map(Join, fff))(s) == Join(Join(fff))(s)
  {
    var (ff, t) := fff(s);
    var (f, u) := ff(t);
    calc {
      Join(Map(Join, fff))(s);
    ==
      f(u);
    ==
      Join(Join(fff))(s);
    }
  }

  lemma {:axiom} TailIsRNG(s: RandomNumberGenerator.RNG)
    ensures RandomNumberGenerator.IsRNG((n: nat) => s(n+1))

  // Equation (2.68) && (2.77)
  lemma {:axiom} HeadIsMeasurable(b: bool)
    ensures
      var e := (iset s | Head(s) == b);
      && e in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(e) == 0.5

  // Equation (2.82)
  lemma {:axiom} MeasureHeadDrop(n: nat, s: RandomNumberGenerator.RNG)
    ensures
      && (iset s | Head(Drop(n, s))) in RandomNumberGenerator.event_space
      && RandomNumberGenerator.mu(iset s | Head(Drop(n, s))) == 0.5

  // Equation (2.78)
  lemma {:axiom} TailIsMeasurePreserving()
    ensures MeasureTheory.IsMeasurePreserving(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, RandomNumberGenerator.event_space, RandomNumberGenerator.mu, Tail)
}

