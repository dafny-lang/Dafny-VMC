/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module CoinModel {
  import RandomNumberGenerator
  import Monad

  function CoinSample(s: RandomNumberGenerator.RNG): (bool, RandomNumberGenerator.RNG) {
    Monad.Deconstruct(s)
  }
}
