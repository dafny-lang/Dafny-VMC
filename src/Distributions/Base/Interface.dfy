/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

include "../../ProbabilisticProgramming/RandomNumberGenerator.dfy"
include "Model.dfy"

module BaseInterface {
  import RandomNumberGenerator
  import BaseModel

  method {:extern "DRandomCoin", "Coin"} ExternCoin() returns (b: bool)

  trait {:termination false} TBase {
    ghost var s: RandomNumberGenerator.RNG

    method Coin() returns (b: bool)
      modifies this
      ensures BaseModel.CoinModel(old(s)) == (b, s)
    {
      b := ExternCoin();
      assume {:axiom} false;
    }

  }
}
