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

  // Definition 33: (weak) independence
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    forall A: iset<A>, E: iset<Rand.Bitstream> | E in Rand.eventSpace :: IsIndepFunctionCondition(f, A, E)
  }

  /*******
   Lemmas
  *******/

  lemma {:axiom} IsIndepImpliesMeasurableBool(f: Monad.Hurd<bool>)
    requires Monad.IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, Monad.boolResultEventSpace, f)

  lemma {:axiom} IsIndepImpliesMeasurableNat(f: Monad.Hurd<nat>)
    requires Monad.IsIndep(f)
    ensures Measures.IsMeasurable(Rand.eventSpace, Monad.natResultEventSpace, f)

  // Equation (3.14)
  lemma {:axiom} IsIndepImpliesIsIndepFunction<A(!new)>(f: Monad.Hurd<A>)
    requires Monad.IsIndep(f)
    ensures IsIndepFunction(f)

  lemma AreIndepEventsConjunctElimination(e1: iset<Rand.Bitstream>, e2: iset<Rand.Bitstream>)
    requires Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
    ensures Rand.prob(e1 * e2) == Rand.prob(e1) * Rand.prob(e2)
  {}
}
