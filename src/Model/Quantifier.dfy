/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "RandomNumberGenerator.dfy"

module Quantifier {
  import opened RandomNumberGenerator

  /************
   Definitions  
  ************/

  ghost predicate ForAllStar(p: RNG -> bool) {
    var e := iset s | p(s);
    && e in event_space
    && mu(e) == 1.0
  }

  ghost predicate ExistsStar(p: RNG -> bool) {
    var e := iset s | p(s);
    && e in event_space
    && mu(e) != 0.0
  }
}