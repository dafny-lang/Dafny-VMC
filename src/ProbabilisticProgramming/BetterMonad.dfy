/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module BetterMonad {
  import Rand
  import Measures
  import Monad
  import Independence
  import Loops

  /************
   Definitions
  ************/

  // The type (monad) of probabilistic computations (cf. Joe Hurd's PhD thesis).
  // For a given stream of bits (coin flips), it yields the result of the computation.
  type BetterHurd<A> = Rand.Bitstream -> Result<A>

  // The result of a probabilistic computation on a bitstream.
  // It either consists of the computed value and the number of consumed bits or indicates nontermination.
  // It differs from Hurd's definition in that the result can be nontermination, which Hurd does not model explicitly.
  datatype Result<A> =
    | Result(value: A, consumed: nat)
    | Diverging
  {
    function Map<B>(f: A -> B): Result<B> {
      match this
      case Diverging => Diverging
      case Result(value, consumed) => Result(f(value), consumed)
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
  }

  ghost function ResultSampleSpace<A(!new)>(sampleSpace: iset<A>): iset<Result<A>> {
    iset r: Result<A> | r.Diverging? || (r.value in sampleSpace && r.consumed in Measures.natSampleSpace)
  }

  ghost function Values<A>(results: iset<Result<A>>): iset<A> {
    iset r <- results | r.Result? :: r.value
  }

  ghost function Consumeds<A>(results: iset<Result<A>>): iset<nat> {
    iset r <- results | r.Result? :: r.consumed
  }

  ghost function ResultEventSpace<A(!new)>(eventSpace: iset<iset<A>>): iset<iset<Result<A>>> {
    iset e: iset<Result<A>> | Values(e) in eventSpace && Consumeds(e) in Measures.natEventSpace
  }

  ghost const boolResultSampleSpace: iset<Result<bool>> := ResultSampleSpace(Measures.boolSampleSpace)

  ghost const boolResultEventSpace: iset<iset<Result<bool>>> := ResultEventSpace(Measures.boolEventSpace)

  ghost const natResultSampleSpace: iset<Result<nat>> := ResultSampleSpace(Measures.natSampleSpace)

  ghost const natResultEventSpace: iset<iset<Result<nat>>> := ResultEventSpace(Measures.natEventSpace)

  ghost function ResultsWithValueIn<A(!new)>(values: iset<A>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.value in values
  }

  ghost function ResultsWithconsumedIn<A(!new)>(consumeds: iset<nat>): iset<Result<A>> {
    iset result: Result<A> | result.Result? && result.consumed in consumeds
  }

  // Equation (3.4)
  function Bind<A,B>(f: BetterHurd<A>, g: A -> BetterHurd<B>): BetterHurd<B> {
    (s: Rand.Bitstream) =>
      match f(s)
      case Diverging => Diverging
      case Result(v, m) =>
        match g(v)(Rand.Drop(m, s))
        case Diverging => Diverging
        case Result(w, n) => Result(w, m + n)
  }

  // Equation (2.42)
  const Coin: BetterHurd<bool> := s => Result(Rand.Head(s), 1)

  function Composition<A,B,C>(f: A -> BetterHurd<B>, g: B -> BetterHurd<C>): A -> BetterHurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Equation (3.3)
  function Return<A>(a: A): BetterHurd<A> {
    (s: Rand.Bitstream) => Result(a, 0)
  }

  // TODO
  function While<A>(condition: A -> bool, body: A -> BetterHurd<A>, init: A): BetterHurd<A>

  function Map<A,B>(m: BetterHurd<A>, f: A -> B): BetterHurd<B> {
    Bind(m, (a: A) => Return(f(a)))
  }

  function Join<A>(ff: BetterHurd<BetterHurd<A>>): BetterHurd<A> {
    Bind(ff, x => x)
  }

  /*******
   Monad Laws
  *******/

  lemma UnitalityBindReturn<A,B>(a: A, g: A -> BetterHurd<B>, s: Rand.Bitstream)
    ensures Bind(Return(a), g)(s) == g(a)(s)
  {}

  lemma DropDrop(s: Rand.Bitstream, m: nat, n: nat)
    ensures Rand.Drop(n, Rand.Drop(m, s)) == Rand.Drop(m + n, s)
  {}

  lemma DropDropGeneral(s: Rand.Bitstream)
    ensures forall m: nat, n: nat :: Rand.Drop(n, Rand.Drop(m, s)) == Rand.Drop(m + n, s)
  {
    forall m: nat, n: nat ensures Rand.Drop(n, Rand.Drop(m, s)) == Rand.Drop(m + n, s) {
      DropDrop(s, m, n);
    }
  }

  lemma DropProperty(s: Rand.Bitstream, n: nat)
    ensures forall i: nat :: Rand.Drop(n, s)(i) == s(n + i)
  {}

  lemma BindIsAssociative<A,B,C>(f: BetterHurd<A>, g: A -> BetterHurd<B>, h: B -> BetterHurd<C>, s: Rand.Bitstream)
    ensures Bind(Bind(f, g), h)(s) == Bind(f, (a: A) => Bind(g(a), h))(s)
  {
    match f(s)
    case Diverging => {}
    case Result(v, l) =>
      match g(v)(Rand.Drop(l, s))
      case Diverging => {}
      case Result(w, m) => DropDrop(s, l, m);
  }

  lemma CompositionIsAssociative<A,B,C,D>(f: A -> BetterHurd<B>, g: B -> BetterHurd<C>, h: C -> BetterHurd<D>, a: A, s: Rand.Bitstream)
    ensures Composition(Composition(f, g), h)(a)(s) == Composition(f, Composition(g, h))(a)(s)
  {
    BindIsAssociative(f(a), g, h, s);
  }

  lemma UnitalityJoinReturn<A>(f: BetterHurd<A>, s: Rand.Bitstream)
    ensures Join(Map(f, Return))(s) == Join(Return(f))(s)
  {}

  lemma JoinIsAssociative<A>(fff: BetterHurd<BetterHurd<BetterHurd<A>>>, s: Rand.Bitstream)
    ensures Join(Map(fff, Join))(s) == Join(Join(fff))(s)
  {
    CompositionIsAssociative((_: ()) => fff, x => x, x => x, (), s);
  }

  /***
  Monad homomorphism
  ***/

  function Embed<A>(m: BetterHurd<A>): Monad.Hurd<A> {
    (s: Rand.Bitstream) =>
      match m(s)
      case Diverging => Monad.Result.Diverging
      case Result(v, n) => Monad.Result.Result(v, Rand.Drop(n, s))
  }

  lemma ReturnIsPreserved<A>(v: A)
    ensures forall s: Rand.Bitstream :: Embed(Return(v))(s) == Monad.Return(v)(s)
  {}

  lemma CoinIsPreserved()
    ensures forall s: Rand.Bitstream :: Embed(Coin)(s) == Monad.Coin(s)
  {}

  lemma BindIsPreserved<A, B>(m: BetterHurd<A>, f: A -> BetterHurd<B>)
    ensures forall s: Rand.Bitstream :: Embed(Bind(m, f))(s) == Monad.Bind(Embed(m), v => Embed(f(v)))(s)
  {
    forall s ensures Embed(Bind(m, f))(s) == Monad.Bind(Embed(m), v => Embed(f(v)))(s) {
      DropDropGeneral(s);
    }
  }

  // TODO
  lemma {:axiom} WhileIsPreserved<A>(condition: A -> bool, body: A -> BetterHurd<A>, init: A)
    ensures forall s: Rand.Bitstream :: Embed(While(condition, body, init))(s) == Loops.While(condition, a => Embed(body(a)), init)(s)

  /***
  Strong independence
  ***/

  ghost predicate IsIndep<A>(m: BetterHurd<A>) {
    forall s: Rand.Bitstream :: IsIndepOn(m, s)

  }

  ghost predicate IsIndepOn<A>(m: BetterHurd<A>, s: Rand.Bitstream) {
    match m(s)
    case Diverging => true
    case Result(v, n) =>
      forall s': Rand.Bitstream | PrefixEqual(n, s, s') :: m(s) == m(s')
  }

  ghost predicate PrefixEqual(n: nat, s: Rand.Bitstream, s': Rand.Bitstream) {
    forall i: nat | i < n :: s(i) == s'(i)
  }

  lemma CoinIsIndep()
    ensures IsIndep(Coin)
  {
    forall s: Rand.Bitstream ensures IsIndepOn(Coin, s) {
      match Coin(s)
      case Diverging => {}
      case Result(v, 1) =>
        forall s': Rand.Bitstream | PrefixEqual(1, s, s') ensures Coin(s) == Coin(s') {}
    }
  }

  lemma ReturnIsIndep<A>(a: A)
    ensures IsIndep(Return(a))
  {}

  lemma BindIsIndep<A, B>(h: BetterHurd<A>, f: A -> BetterHurd<B>)
    requires IsIndep(h)
    requires forall a: A :: IsIndep(f(a))
    ensures IsIndep(Bind(h, f))
  {
    forall s: Rand.Bitstream ensures IsIndepOn(Bind(h, f), s) {
      match h(s)
      case Diverging => {}
      case Result(v, m) =>
        var t := Rand.Drop(m, s);
        match f(v)(t)
        case Diverging => {}
        case Result(w, n) => {
          DropDrop(s, m, n);
          forall s': Rand.Bitstream | PrefixEqual(m + n, s, s') ensures Bind(h, f)(s) == Bind(h, f)(s') {
            assert PrefixEqual(m, s, s');
            assert IsIndepOn(h, s);
            assert h(s) == h(s');
            DropDrop(s', m, n);
            var t' := Rand.Drop(m, s');
            assert PrefixEqual(n, t, t') by {
              forall i: nat | i < n ensures t(i) == t'(i) {
                calc {
                  t(i);
                  { DropProperty(s, m); }
                  s(m + i);
                  s'(m + i);
                  { DropProperty(s', m); }
                  t'(i);
                }
              }
            }
            assert IsIndepOn(f(v), t);
            assert f(v)(t) == f(v)(t');
          }
        }
    }
  }

  lemma {:axiom} WhileIsIndep<A>(condition: A -> bool, body: A -> BetterHurd<A>, init: A)
    ensures IsIndep(While(condition, body, init))

  lemma StrongIndependenceImpliesWeakIndependence<A>(m: BetterHurd<A>)
    requires IsIndep(m)
    ensures Independence.IsIndepFunction(Embed(m))
  {
    assume {:axiom} false;
  }
}

