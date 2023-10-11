/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Independence {
  import Monad
  import RandomNumberGenerator
  import MeasureTheory
  import Quantifier

  /************
   Definitions
  ************/

  ghost predicate TerminatesAlmostSurely<A>(f: Monad.Hurd<A>) {
    Quantifier.ForAllStar((s: RandomNumberGenerator.RNG) => f(s).Terminating?)
  }

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Monad.Hurd<A>, A: iset<A>, E: iset<RandomNumberGenerator.RNG>) {
    var e1 := Monad.rngsWithResultValue(f, v => v in A);
    var e2 := Monad.rngsWithResultRng(f, s => s in E);
    MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2)
  }

  // Definition 33
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    && TerminatesAlmostSurely(f)
    && forall A: iset<A>, E: iset<RandomNumberGenerator.RNG> | E in RandomNumberGenerator.event_space :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35
  ghost predicate {:axiom} IsIndepFn<A(!new)>(f: Monad.Hurd<A>)

  /*******
   Lemmas
  *******/

  lemma {:axiom} IsIndepFnImpliesFstMeasurableBool(f: Monad.Hurd<bool>)
    requires IsIndepFn(f)
    ensures MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, MeasureTheory.partialBoolEventSpace, s => f(s).Value())

  lemma {:axiom} IsIndepFnImpliesFstMeasurableNat(f: Monad.Hurd<nat>)
    requires IsIndepFn(f)
    ensures MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, MeasureTheory.partialNatEventSpace, s => f(s).Value())

  lemma {:axiom} IsIndepFnImpliesSndMeasurable<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndepFn(f)
    ensures MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.partial_event_space, s => f(s).Rng())

  lemma {:axiom} IsIndepFnImpliesIsIndepFunction<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndepFn(f)
    ensures IsIndepFunction(f)

  // Equation (3.17)
  lemma {:axiom} DeconstructIsIndepFn()
    ensures IsIndepFn(Monad.Deconstruct)

  // Equation (3.18)
  lemma {:axiom} ReturnIsIndepFn<T>(x: T)
    ensures IsIndepFn(Monad.Return(x))

  // Equation (3.19)
  lemma {:axiom} IndepFnIsCompositional<A, B>(f: Monad.Hurd<A>, g: A -> Monad.Hurd<B>)
    requires IsIndepFn(f)
    requires forall a :: IsIndepFn(g(a))
    ensures IsIndepFn(Monad.Bind(f, g))

  lemma AreIndepEventsConjunctElimination(e1: iset<RandomNumberGenerator.RNG>, e2: iset<RandomNumberGenerator.RNG>)
    requires MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2)
    ensures RandomNumberGenerator.mu(e1 * e2) == RandomNumberGenerator.mu(e1) * RandomNumberGenerator.mu(e2)
  {}
}
