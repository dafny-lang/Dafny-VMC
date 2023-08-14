include "Monad.dfy"
include "RandomNumberGenerator.dfy"

module Geometric {
  import opened Monad
  import opened RandomNumberGenerator

  /************
   Definitions  
  ************/

  // Equation (4.17)
  function ProbGeometricIter(b: bool, n: nat): Hurd<(bool, nat)> {
    var f := (b': bool) => Return(b', n + 1);
    Bind(Deconstruct, f)
  }  

  // Equation (4.18)
  function ProbGeometric(): Hurd<nat> {
    var fst := ((x, _): (bool, nat)) => x;
    var f := ((b, n): (bool, nat)) => Return(n - 1);
    Bind(ProbWhile(fst, ProbGeometricIter(true, 0)), f)
  }

  /*******
   Lemmas  
  *******/

  // Equation (4.19)
  lemma {:axiom} ProbGeometricIsIndepFn()
    ensures IsIndepFn(ProbGeometric)
  
  // Equation (4.20)
  lemma {:axiom} ProbGeometricCorrectness()
    ensures 

}

