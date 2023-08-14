/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Monad.dfy"
include "RandomNumberGenerator.dfy"

module Bernoulli {
  import opened Monad
  import opened RandomNumberGenerator

  /************
   Definitions  
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0

  // Equation (4.23)
  function ProbBernoulli(p: Probability): Hurd<bool> {
    assume {:axiom} false;
    var f :=
      (b: bool) =>
        if b then
          if p <= 0.5 then
            Return(false)
          else
            ProbBernoulli(2.0 * p - 1.0)
        else
        if p <= 0.5 then
          ProbBernoulli(2.0 * p)
        else
          Return(true);
    Bind(Deconstruct, f)
  }  

  /*******
   Lemmas  
  *******/

  lemma {:axiom} BernoulliCorrectness(p: Probability)
    ensures 
      var e := iset s | ProbBernoulli(p)(s).0;
      && e in event_space
      && mu(e) == p
  

}

