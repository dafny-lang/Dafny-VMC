/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module Model {
  import RandomNumberGenerator
  import Monad

  function Sample(s: RandomNumberGenerator.RNG): (bool, RandomNumberGenerator.RNG) {
    Monad.Deconstruct(s)
  }
}
