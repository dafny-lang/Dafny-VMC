/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "Model.dfy"

module Base {
  import opened RandomNumberGenerator
  import opened BaseModel

  trait {:termination false} Base {
    ghost var s: RNG

    method {:extern} Coin() returns (b: bool)
      modifies this
      ensures CoinModel(old(s)) == (b, s)

  }
}
