/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "RandomNumberGenerator.dfy"
include "MeasureTheory.dfy"

module Monad {
  import opened RandomNumberGenerator
  import opened MeasureTheory

  /************
   Definitions  
  ************/

  type Hurd<A> = RNG -> (A, RNG)

  // Equation (2.38)
  function Tail(s: RNG): (s': RNG) {
    TailIsRNG(s);
    (n: nat) => s(n+1)
  }

  // Equation (2.37)
  function Head(s: RNG): bool {
    s(0)
  }

  // Equation (2.42)
  function Deconstruct(s: RNG): (bool, RNG) {
    (Head(s), Tail(s))
  }

  // Equation (2.41)
  function Drop(n: nat, s: RNG): (s': RNG)
    ensures Head(s') == s(n)
  {
    if n == 0 then
      s
    else
      Drop(n - 1, Tail(s))
  }

  // Equation (3.4)
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: RNG) =>
      var (a, s') := f(s);
      g(a)(s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): Hurd<A> {
    (s: RNG) => (a, s)
  }

  function Map<A,B>(f: A -> B, m: Hurd<A>): Hurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  /*******
   Lemmas  
  *******/

  lemma {:axiom} TailIsRNG(s: RNG)
    ensures IsRNG((n: nat) => s(n+1))

  // Equation (2.68) && (2.77)
  lemma {:axiom} HeadIsMeasurable(b: bool)
    ensures
      var e := (iset s | Head(s) == b);
      && e in event_space
      && mu(e) == 0.5

  // Equation (2.82)
  lemma {:axiom} MeasureHeadDrop(n: nat, s: RNG)
    ensures
      && (iset s | Head(Drop(n, s))) in event_space
      && mu(iset s | Head(Drop(n, s))) == 0.5

  // Equation (2.78)
  lemma {:axiom} TailIsMeasurePreserving()
    ensures IsMeasurePreserving(event_space, mu, event_space, mu, Tail)
}

