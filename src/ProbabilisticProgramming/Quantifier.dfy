/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Quantifier {
  import Rand

  /************
   Definitions
  ************/

  ghost predicate AlmostSurely(p: Rand.Bitstream -> bool) {
    var e := iset s | p(s);
    && e in Rand.eventSpace
    && Rand.prob(e) == 1.0
  }

  ghost predicate WithPosProb(p: Rand.Bitstream -> bool) {
    var e := iset s | p(s);
    && e in Rand.eventSpace
    && Rand.prob(e) > 0.0
  }
}
