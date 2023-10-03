/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"

module GeometricModel {
  import Monad
  import WhileAndUntil

  // Equation (4.18)
  function Sample(): Monad.Hurd<int> {
    var fst := (t: (bool, int)) => t.0;
    var f := (t: (bool, int)) => Monad.Return(t.1 - 1);
    ProbWhileGeometricTerminates();
    var g := WhileAndUntil.ProbWhile(fst, GeometricIter, (true, 0));
    Monad.Bind(g, f)
  }

  // Equation (4.17)
  function GeometricIter(t: (bool, int)): (f: Monad.Hurd<(bool, int)>)
    ensures forall s :: f(s) == ((Monad.Head(s), t.1 + 1), Monad.Tail(s))
  {
    Monad.Bind(Monad.Deconstruct, (b': bool) => Monad.Return((b', t.1 + 1)))
  }

  lemma {:axiom} ProbWhileGeometricTerminates()
    ensures
      var fst := (t: (bool, int)) => t.0;
      WhileAndUntil.ProbWhileTerminates(GeometricIter, fst)

}