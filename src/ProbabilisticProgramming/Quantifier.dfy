/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "RandomNumberGenerator.dfy"

module Quantifier {
  import RandomNumberGenerator

  /************
   Definitions  
  ************/

  ghost predicate ForAllStar(p: RandomNumberGenerator.RNG -> bool) {
    var e := iset s | p(s);
    && e in RandomNumberGenerator.event_space
    && RandomNumberGenerator.mu(e) == 1.0
  }

  ghost predicate ExistsStar(p: RandomNumberGenerator.RNG -> bool) {
    var e := iset s | p(s);
    && e in RandomNumberGenerator.event_space
    && RandomNumberGenerator.mu(e) != 0.0
  }
}