include "RandomNumberGenerator.dfy"
include "Monad.dfy"
include "MeasureTheory.dfy"

module Independence {
  import opened Monad
  import opened RandomNumberGenerator
  import opened MeasureTheory

  /************
   Definitions  
  ************/

  // Definition 33
  ghost predicate IsIndepFunctionCondition<A(!new)>(f: Hurd<A>, A: iset<A>, E: iset<RNG>) {
    var e1 := iset s | f(s).1 in E;
    var e2 := iset s | f(s).0 in A;
    AreIndepEvents(event_space, mu, e1, e2)
  }

  // Definition 33
  ghost predicate IsIndepFunction<A(!new)>(f: Hurd<A>) {
    forall A: iset<A>, E: iset<RNG> | E in event_space :: IsIndepFunctionCondition(f, A, E)
  }

  // Definition 35
  ghost predicate {:axiom} IsIndepFn<A>(f: Hurd<A>)
    ensures IsIndepFunction(f)
    ensures IsMeasurable(event_space, event_space, s => f(s).1)

  /*******
   Lemmas  
  *******/

  // Equation (3.17)
  lemma {:axiom} DeconstructIsIndepFn()
    ensures IsIndepFn(Deconstruct)

  // Equation (3.18)
  lemma {:axiom} ReturnIsIndepFn<T>(x: T)
    ensures IsIndepFn(Return(x))

  // Equation (3.19)
  lemma {:axiom} IndepFnIsCompositional<A, B>(f: Hurd<A>, g: A -> Hurd<B>)
    requires IsIndepFn(f)
    requires forall a :: IsIndepFn(g(a))
    ensures IsIndepFn(Bind(f, g))

  lemma AreIndepEventsConjunctElimination(e1: iset<RNG>, e2: iset<RNG>)
    requires AreIndepEvents(event_space, mu, e1, e2)
    ensures mu(e1 * e2) == mu(e1) * mu(e2)
  {}
}