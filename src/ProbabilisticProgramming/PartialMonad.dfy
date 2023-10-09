/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Partial {
  import Monad
  import RandomNumberGenerator
  import MeasureTheory

  /************
   Definitions
  ************/

  datatype Wrap<T> = Diverging | Terminating(value: T) {
    predicate IsFailure() {
      Diverging?
    }

    function PropagateFailure(): Wrap<T> {
      Diverging
    }

    function Extract(): T
      requires !IsFailure()
    {
      this.value
    }

    function Map<U>(f: T -> U): Wrap<U> {
      match this
      case Terminating(value) => Terminating(f(value))
      case Diverging => Diverging
    }

    function UnwrapOr(default: T): T {
      match this
      case Terminating(value) => value
      case Diverging => default
    }

    function Satisfies(f: T -> bool): bool {
      this.Map(f).UnwrapOr(false)
    }

    function Bind<U>(f: T -> Wrap<U>): Wrap<U> {
      match this
      case Terminating(value) => f(value)
      case Diverging => Diverging
    }
  }

  type Hurd<A> = RandomNumberGenerator.RNG -> (Wrap<A>, RandomNumberGenerator.RNG)

  // Equation (3.4)
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: RandomNumberGenerator.RNG) =>
      var (a, s') := f(s);
      match a
      case Terminating(a) => g(a)(s')
      case Diverging => (Diverging, s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  function Diverge<A>(): Hurd<A> {
    Monad.Return(Diverging)
  }

  function Return<A>(a: A): Hurd<A> {
    Monad.Return(Terminating(a))
  }

  function Flatten<A>(f: Hurd<Wrap<A>>): Hurd<A> {
    Bind(f, (a: Wrap<A>) =>
      match a
      case Terminating(a) => Return(a)
      case Diverging => Diverge())
  }

  function Map<A,B>(f: A -> B, m: Hurd<A>): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    Bind(ff, a => a)
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
    assume {:axiom} false; // todo
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
    assume {:axiom} false; // todo
  }
}

