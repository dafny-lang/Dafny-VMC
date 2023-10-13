/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Independence {
  import Monad
  import Random
  import Measures

  /************
   Definitions
  ************/

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Monad.Hurd<A>, A: iset<A>, E: iset<Random.Bitstream>) {
    var e1 := iset s | f(s).1 in E;
    var e2 := iset s | f(s).0 in A;
    Measures.AreIndepEvents(Random.eventSpace, Random.Prob, e1, e2)
  }

  // Definition 33
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    forall A: iset<A>, E: iset<Random.Bitstream> | E in Random.eventSpace :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35
  ghost predicate {:axiom} IsIndep<A(!new)>(f: Monad.Hurd<A>)

  /*******
   Lemmas
  *******/

  lemma {:axiom} IsIndepImpliesFstMeasurableBool(f: Monad.Hurd<bool>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Random.eventSpace, Measures.boolEventSpace, s => f(s).0)

  lemma {:axiom} IsIndepImpliesFstMeasurableNat(f: Monad.Hurd<nat>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Random.eventSpace, Measures.natEventSpace, s => f(s).0)

  lemma {:axiom} IsIndepImpliesSndMeasurable<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndep(f)
    ensures Measures.IsMeasurable(Random.eventSpace, Random.eventSpace, s => f(s).1)

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
  lemma {:axiom} IndepFnIsCompositional<A, B>(f: Monad.Hurd<A>, g: A -> Monad.Hurd<B>)
    requires IsIndep(f)
    requires forall a :: IsIndep(g(a))
    ensures IsIndep(Monad.Bind(f, g))

  lemma AreIndepEventsConjunctElimination(e1: iset<Random.Bitstream>, e2: iset<Random.Bitstream>)
    requires Measures.AreIndepEvents(Random.eventSpace, Random.Prob, e1, e2)
    ensures Random.Prob(e1 * e2) == Random.Prob(e1) * Random.Prob(e2)
  {}
}
