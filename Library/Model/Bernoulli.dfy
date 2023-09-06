/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "Monad.dfy"
include "RandomNumberGenerator.dfy"
include "Independence.dfy"

module Bernoulli {
  import opened Monad
  import opened RandomNumberGenerator
  import opened Independence

  /************
   Definitions  
  ************/

  type Probability = x: real | 0.0 <= x <= 1.0

  // Equation (4.23)
  function ProbBernoulli(p: Probability): Hurd<bool> {
    assume {:axiom} false; // Assume termination
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

  function ProbBernoulliNext(p': Probability, b: bool): (p: Probability)
    requires (b && p' > 0.5) || (!b && p' <= 0.5)
  {
    if (b && p' > 0.5) then 
      2.0 * p' - 1.0
    else
      2.0 * p'
  }

  function ProbBernoulliCurried(p: Probability, s: RNG): (t: (bool, RNG))
    ensures t == ProbBernoulli(p)(s)
  {
    if Head(s) then
      if p <= 0.5 then 
        (false, Tail(s))
      else
        assume {:axiom} false; // Assume termination
        ProbBernoulliCurried(2.0 * p - 1.0, Tail(s))
    else
      if p <= 0.5 then
        assume {:axiom} false; // Assume termination
        ProbBernoulliCurried(2.0 * p, Tail(s))
      else
        (true, Tail(s))
  }

/*   function ProbBernoulli(p: Probability, s: RNG, ghost w: nat): (bool, RNG)
    decreases w
  {
    assume {:axiom} w != 0; // Assume termination

    if Head(s) then 
      if p <= 0.5 then 
        (false, s)
      else 
        ProbBernoulli(2.0 * p - 1.0, Tail(s), w - 1)
    else 
      if p <= 0.5 then
        ProbBernoulli(2.0 * p, Tail(s), w - 1)
      else
        (true, s)
  }   */

  /*******
   Lemmas  
  *******/

  lemma {:axiom} ProbBernoulliIsIndepFn(p: Probability, w: nat)
    ensures IsIndepFn(ProbBernoulli(p))

  lemma {:axiom} BernoulliCorrectness(p: Probability, w: nat)
    ensures 
      var e := iset s | ProbBernoulli(p)(s).0;
      && e in event_space
      && mu(e) == p
  

}

