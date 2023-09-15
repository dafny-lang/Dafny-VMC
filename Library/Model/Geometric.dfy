/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Monad.dfy"
include "RandomNumberGenerator.dfy"
include "WhileAndUntil.dfy"
include "Independence.dfy"
include "Helper.dfy"

module Geometric {
  import opened Monad
  import opened RandomNumberGenerator
  import opened WhileAndUntil
  import opened Independence
  import opened Helper

  /************
   Definitions  
  ************/

  // Equation (4.17)
  function ProbGeometricIter(): (f: ((bool, int)) -> Hurd<(bool, int)>)
    ensures forall t: (bool, int), s :: f(t)(s) == ((Head(s), t.1 + 1), Tail(s))
  {
    var g := (t: (bool, int)) => 
      var f := (b': bool) => Return((b', t.1 + 1));
      Bind(Deconstruct, f);
    g
  }  

  // Equation (4.18)
  function ProbGeometric(): Hurd<int> {
    var fst := (t: (bool, int)) => t.0;
    var f := (t: (bool, int)) => Return(t.1 - 1);
    ProbWhileGeometricTerminates();
    var g := ProbWhile(fst, ProbGeometricIter(), (true, 0));
    Bind(g, f)
  }

  /*******
   Lemmas  
  *******/

  lemma {:axiom} ProbWhileGeometricTerminates()
    ensures 
      var fst := (t: (bool, int)) => t.0;
      ProbWhileTerminates(ProbGeometricIter(), fst)

  // Equation (4.19)
  lemma {:axiom} ProbGeometricIsIndepFn()
    ensures IsIndepFn(ProbGeometric())
  
  // Equation (4.20)
  lemma {:axiom} ProbGeometricCorrectness(n: nat)
    ensures
      var e := iset s | ProbGeometric()(s).0 == n;
      && e in event_space
      && mu(e) == RealPower(1.0 / 2.0, n + 1)

}

