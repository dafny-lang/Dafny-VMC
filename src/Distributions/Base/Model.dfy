/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "../../ProbabilisticProgramming/Monad.dfy"

module BaseModel {
  import opened RandomNumberGenerator
  import opened Monad

  function CoinModel(s: RNG): (bool, RNG) {
    Monad.Deconstruct(s)
  }
}
