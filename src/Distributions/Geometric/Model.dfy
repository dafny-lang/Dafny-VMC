/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/Monad.dfy"
include "../../ProbabilisticProgramming/WhileAndUntil.dfy"
include "../../ProbabilisticProgramming/Independence.dfy"
include "Correctness.dfy"

import opened Monad
import opened WhileAndUntil
import opened Independence

// Equation (4.18)
function ProbGeometric(): Hurd<int> {
  var fst := (t: (bool, int)) => t.0;
  var f := (t: (bool, int)) => Return(t.1 - 1);
  ProbWhileGeometricTerminates();
  var g := ProbWhile(fst, ProbGeometricIter, (true, 0));
  Bind(g, f)
}

// Equation (4.17)
function ProbGeometricIter(t: (bool, int)): (f: Hurd<(bool, int)>)
  ensures forall s :: f(s) == ((Head(s), t.1 + 1), Tail(s))
  ensures IsIndepFn(f)
{
  var g := (b': bool) => Return((b', t.1 + 1));
  assert forall b' :: IsIndepFn(g(b')) by {
    forall b' ensures IsIndepFn(g(b')) {
      ReturnIsIndepFn((b', t.1 + 1));
    }
  }
  var f := Bind(Deconstruct, g);
  assert IsIndepFn(f) by {
    DeconstructIsIndepFn();
    IndepFnIsCompositional(Deconstruct, g);
  }
  f
}
