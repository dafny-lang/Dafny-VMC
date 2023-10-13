/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

module Quantifier {
  import Random

  /************
   Definitions
  ************/

  ghost predicate AlmostSurely(p: Random.Bitstream -> bool) {
    var e := iset s | p(s);
    && e in Random.eventSpace
    && Random.Prob(e) == 1.0
  }

  ghost predicate WithPosProb(p: Random.Bitstream -> bool) {
    var e := iset s | p(s);
    && e in Random.eventSpace
    && Random.Prob(e) != 0.0
  }
}
