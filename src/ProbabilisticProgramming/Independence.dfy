/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Independence {
  import Monad
  import Rand
  import Measures

  /************
   Definitions
  ************/

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Monad.Hurd<A>, A: iset<A>, E: iset<Rand.Bitstream>) {
    var e1 := iset s | f(s).RestIn(E);
    var e2 := iset s | f(s).In(A);
    Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
  }

  // Definition 33
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    forall A: iset<A>, E: iset<Rand.Bitstream> | E in Rand.eventSpace :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35
  ghost predicate {:axiom} IsIndep<A(!new)>(f: Monad.Hurd<A>)

  /*******
   Lemmas
  *******/

  lemma {:axiom} IsIndepImpliesValueMeasurableBool(f: Monad.Hurd<bool>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, Measures.boolEventSpace, s => f(s).value)

  lemma {:axiom} IsIndepImpliesValueMeasurableNat(f: Monad.Hurd<nat>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, Measures.natEventSpace, s => f(s).value)

  lemma {:axiom} IsIndepImpliesRestMeasurable<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, Rand.eventSpace, s => f(s).rest)

  lemma {:axiom} IsIndepImpliesIsIndepFunction<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndep(f)
    ensures IsIndepFunction(f)

  // Equation (3.17)
  lemma {:axiom} CoinIsIndep()
    ensures IsIndep(Monad.Coin)

  // Equation (3.18)
  lemma {:axiom} ReturnIsIndep<T>(x: T)
    ensures IsIndep(Monad.Return(x))

  // Equation (3.19)
  lemma {:axiom} BindIsIndep<A, B>(f: Monad.Hurd<A>, g: A -> Monad.Hurd<B>)
    requires IsIndep(f)
    requires forall a :: IsIndep(g(a))
    ensures IsIndep(Monad.Bind(f, g))

  lemma AreIndepEventsConjunctElimination(e1: iset<Rand.Bitstream>, e2: iset<Rand.Bitstream>)
    requires Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
    ensures Rand.prob(e1 * e2) == Rand.prob(e1) * Rand.prob(e2)
  {}
}
