/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "Model.dfy"

import opened RandomNumberGenerator

trait Base {
  ghost var s: RNG

  method {:extern} Coin() returns (b: bool)
    modifies this
    ensures BaseModel.CoinModel(old(s)) == (b, s)

}
