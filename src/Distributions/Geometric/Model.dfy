/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "../../ProbabilisticProgramming/Quantifier.dfy"

module GeometricModel {
  import Monad
  import WhileAndUntil
  import Independence
  import Quantifier

  // Equation (4.18)
  function Sample(): Monad.Hurd<int> {
    var fst := (t: (bool, int)) => t.0;
    var f := (t: (bool, int)) => Monad.Return(t.1 - 1);
    ProbWhileGeometricTerminates();
    var g := WhileAndUntil.ProbWhile(fst, SampleIter, (true, 0));
    Monad.Bind(g, f)
  }

  // Equation (4.17)
  function SampleIter(t: (bool, int)): (f: Monad.Hurd<(bool, int)>)
    ensures forall s :: f(s) == ((Monad.Head(s), t.1 + 1), Monad.Tail(s))
    ensures Independence.IsIndepFn(f)
  {
    var g := (b': bool) => Monad.Return((b', t.1 + 1));
    assert forall b' :: Independence.IsIndepFn(g(b')) by {
      forall b' ensures Independence.IsIndepFn(g(b')) {
        Independence.ReturnIsIndepFn((b', t.1 + 1));
      }
    }
    var f := Monad.Bind(Monad.Deconstruct, g);
    assert Independence.IsIndepFn(f) by {
      Independence.DeconstructIsIndepFn();
      Independence.IndepFnIsCompositional(Monad.Deconstruct, g);
    }
    f
  }

  lemma ProbWhileGeometricTerminates()
    ensures
      var fst := (t: (bool, int)) => t.0;
      WhileAndUntil.ProbWhileTerminates(SampleIter, fst)
  {
    var fst := (t: (bool, int)) => t.0;
    assert forall t :: Independence.IsIndepFn(SampleIter(t));
    assert forall t :: Quantifier.ExistsStar(WhileAndUntil.Helper(SampleIter, fst, t)) by {
      assume {:axiom} false;
    }
    WhileAndUntil.EnsureProbWhileTerminates(SampleIter, fst);
  }

}