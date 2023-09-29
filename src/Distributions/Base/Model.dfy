/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BaseModel {
  import RandomNumberGenerator
  import Monad

  function CoinModel(s: RandomNumberGenerator.RNG): (bool, RandomNumberGenerator.RNG) {
    Monad.Deconstruct(s)
  }
}
