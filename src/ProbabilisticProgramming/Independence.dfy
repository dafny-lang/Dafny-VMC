/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "RandomNumberGenerator.dfy"
include "Monad.dfy"
include "../Math/MeasureTheory.dfy"

module Independence {
  import Monad
  import RandomNumberGenerator
  import MeasureTheory

  /************
   Definitions
  ************/

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Monad.Hurd<A>, A: iset<A>, E: iset<RandomNumberGenerator.RNG>) {
    var e1 := iset s | f(s).1 in E;
    var e2 := iset s | f(s).0 in A;
    MeasureTheory.AreIndepEvents(RandomNumberGenerator.event_space, RandomNumberGenerator.mu, e1, e2)
  }

  // Definition 33
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    forall A: iset<A>, E: iset<RandomNumberGenerator.RNG> | E in RandomNumberGenerator.event_space :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35
  ghost predicate {:axiom} IsIndepFn<A(!new)>(f: Monad.Hurd<A>)

  /*******
   Lemmas
  *******/

  lemma {:axiom} IsIndepFnImpliesMeasurable<A(!new)>(f: Monad.Hurd<A>)
    requires IsIndepFn(f)
    ensures MeasureTheory.IsMeasurable(RandomNumberGenerator.event_space, RandomNumberGenerator.event_space, s => f(s).1)

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
