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
    Measures.AreIndepEvents(
      Rand.eventSpace,
      Rand.prob,
      Monad.BitstreamsWithValueIn(f, A),
      Monad.BitstreamsWithRestIn(f, E))
  }

  // Definition 33: (weak) independence
  ghost predicate IsIndepFunction<A(!new)>(f: Monad.Hurd<A>) {
    forall A: iset<A>, E: iset<Rand.Bitstream> | E in Rand.eventSpace :: IsIndepFunctionCondition(f, A, E)
  }

  /*******
   Lemmas
  *******/

  lemma ResultsIndependent<A(!new)>(
    h: Monad.Hurd<A>,
    aSet: iset<A>,
    bSeeds: iset<Rand.Bitstream>
  )
    requires hIndep: IsIndepFunction(h)
    requires bMeasurable: bSeeds in Rand.eventSpace
    requires hIsMeasurePreserving: Measures.IsMeasurePreserving(Rand.eventSpace, Rand.prob, Rand.eventSpace, Rand.prob, s => h(s).rest)
    ensures Rand.prob(Monad.BitstreamsWithValueIn(h, aSet) * Monad.BitstreamsWithRestIn(h, bSeeds)) == Rand.prob(Monad.BitstreamsWithValueIn(h, aSet)) * Rand.prob(bSeeds)
  {
    var aSeeds := Monad.BitstreamsWithValueIn(h, aSet);
    var restBSeeds := Monad.BitstreamsWithRestIn(h, bSeeds);
    assert Rand.prob(aSeeds * restBSeeds) == Rand.prob(aSeeds) * Rand.prob(restBSeeds) by {
      reveal hIndep;
      reveal bMeasurable;
      assert IsIndepFunction(h);
      assert IsIndepFunctionCondition(h, aSet, bSeeds);
      assert Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, aSeeds, restBSeeds);
    }
    assert Rand.prob(restBSeeds) == Rand.prob(bSeeds) by {
      calc {
        Rand.prob(restBSeeds);
        Rand.prob(Monad.BitstreamsWithRestIn(h, bSeeds));
        { assert Monad.BitstreamsWithRestIn(h, bSeeds) == iset s | h(s).rest in bSeeds; }
        Rand.prob(iset s | h(s).rest in bSeeds);
        { assert (iset s | h(s).rest in bSeeds) == Measures.PreImage(s => h(s).rest, bSeeds); }
        Rand.prob(Measures.PreImage(s => h(s).rest, bSeeds));
        { reveal bMeasurable; reveal hIsMeasurePreserving; }
        Rand.prob(bSeeds);
      }
    }
  }

  lemma AreIndepEventsConjunctElimination(e1: iset<Rand.Bitstream>, e2: iset<Rand.Bitstream>)
    requires Measures.AreIndepEvents(Rand.eventSpace, Rand.prob, e1, e2)
    ensures Rand.prob(e1 * e2) == Rand.prob(e1) * Rand.prob(e2)
  {}
}